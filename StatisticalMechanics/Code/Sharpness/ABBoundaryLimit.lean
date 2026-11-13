/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Sharpness.ABBoundaryPhi
import Code.Sharpness.ABLatticeUnconditional

open Filter Finset MeasureTheory Set SimpleGraph Topology

namespace StatMech
namespace Sharpness

open ConfigSpace Lattice
open StatMech.Percolation

@[simp] theorem abbl_abbEdgeEquiv_symm_mk {U W : Type*}
    (sigma : U ≃ W) (a b : W) :
    (abbEdgeEquiv sigma).symm s(a, b) = s(sigma.symm a, sigma.symm b) := by
  apply (abbEdgeEquiv sigma).injective
  simp [abbEdgeEquiv_mk]

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

set_option maxHeartbeats 800000 in




theorem abbl_residual_le_exp (J : Sym2 V → Real) (o : V)
    (beta h : Real) (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) (k : Nat)
    (R : Set (ConfigSpace (Sym2 (Option V))))
    (hRghost : R ⊆
      (connEvent (withGhost G) Set.univ (some o) {none})ᶜ)
    (hcard : ∀ eta : {e // e ∉ FieldGhostDict.ghostEdges V} → Bool,
      ∀ gamma : {e // e ∈ FieldGhostDict.ghostEdges V} → Bool,
        abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈ R →
          k ≤ (abgrActiveGhost G o eta).card) :
    probV (abfaParams G J beta h) R ≤
      Real.exp (-(h * (k : Real))) := by
  let D := FieldGhostDict.ghostEdges V
  let q := qField h
  let p : Sym2 (Option V) → Real := fun e ↦
    pBeta (abfaLiftCoupling G J e) beta
  have hq0 : 0 ≤ q := (qField_mem h hh).1
  have hq1 : q ≤ 1 := (qField_mem h hh).2
  have hsplit :
      probV (abfaParams G J beta h) R =
        ∑ eta : {e // e ∉ D} → Bool,
          abgrOffWeight G J beta eta *
            probV (fun _ : {e // e ∈ D} ↦ q)
              {gamma | abgrMerge D gamma eta ∈ R} := by
    unfold abfaParams abpdBetaFieldParams
    simpa only [D, q, p, abgrOffWeight] using
      (abgr_probV_split D q p R)
  rw [hsplit]
  have hsection : ∀ eta : {e // e ∉ D} → Bool,
      probV (fun _ : {e // e ∈ D} ↦ q)
          {gamma | abgrMerge D gamma eta ∈ R} ≤
        Real.exp (-(h * (k : Real))) := by
    intro eta
    by_cases hne : ({gamma | abgrMerge D gamma eta ∈ R} :
        Set ({e // e ∈ D} → Bool)).Nonempty
    · obtain ⟨gamma0, hgamma0⟩ := hne
      have hk : k ≤ (abgrActiveGhost G o eta).card :=
        hcard eta gamma0 hgamma0
      let C : Set ({e // e ∈ D} → Bool) :=
        {gamma | ∀ e ∈ abgrActiveGhost G o eta, gamma e = false}
      have hsub : {gamma | abgrMerge D gamma eta ∈ R} ⊆ C := by
        intro gamma hgamma e he
        by_contra hopen
        have hopen' : gamma e = true := by
          cases hge : gamma e <;> simp_all
        have hconn : abgrMerge D gamma eta ∈
            connEvent (withGhost G) Set.univ (some o) {none} :=
          (abgr_section_iff_anyOpen G o gamma eta).mpr ⟨e, he, hopen'⟩
        exact (hRghost hgamma) hconn
      have hmono := abgi_probV_mono (fun _ : {e // e ∈ D} ↦ q)
        (fun _ ↦ ⟨hq0, hq1⟩) hsub
      have hclosed :
          probV (fun _ : {e // e ∈ D} ↦ q) C =
            Real.exp (-(h * ((abgrActiveGhost G o eta).card : Real))) := by
        rw [show C = {gamma | ∀ e ∈ abgrActiveGhost G o eta,
            gamma e = false} by rfl,
          abgr_probV_allClosed]
        have hprofile := abgr_cluster_profile_eq_exp h
          (abgrActiveGhost G o eta).card
        simp only [q, qField, sub_sub_cancel, Finset.prod_const,
          Finset.card_attach] at hprofile ⊢
        linarith
      rw [hclosed] at hmono
      exact hmono.trans (Real.exp_le_exp.mpr (by
        have hcast : (k : Real) ≤ (abgrActiveGhost G o eta).card := by
          exact_mod_cast hk
        nlinarith))
    · have hempty : {gamma | abgrMerge D gamma eta ∈ R} =
          (∅ : Set ({e // e ∈ D} → Bool)) := Set.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]
      simp only [probV, Set.indicator_empty, zero_mul, Finset.sum_const_zero]
      exact (Real.exp_pos _).le
  calc
    (∑ eta : {e // e ∉ D} → Bool,
        abgrOffWeight G J beta eta *
          probV (fun _ : {e // e ∈ D} ↦ q)
            {gamma | abgrMerge D gamma eta ∈ R}) ≤
      ∑ eta : {e // e ∉ D} → Bool,
        abgrOffWeight G J beta eta *
          Real.exp (-(h * (k : Real))) := by
      apply Finset.sum_le_sum
      intro eta heta
      exact mul_le_mul_of_nonneg_left (hsection eta)
        (abgr_offWeight_nonneg G J beta hJ hbeta eta)
    _ = Real.exp (-(h * (k : Real))) := by
      rw [← Finset.sum_mul, abgr_sum_offWeight G J beta, one_mul]



theorem abbl_closeGhost_conn_of_not_ghost (o y : V)
    (omega : ConfigSpace (Sym2 (Option V)))
    (hconn : omega ∈
      connEvent (withGhost G) Set.univ (some o) {some y})
    (hnot : omega ∉
      connEvent (withGhost G) Set.univ (some o) {none}) :
    abgrCloseGhost omega ∈
      connEvent (withGhost G) Set.univ (some o) {some y} := by
  obtain ⟨_, z, _, hz, ⟨p⟩⟩ := hconn
  have hzy : z = some y := Set.mem_singleton_iff.mp hz
  subst z
  let q : (openSub (withGhost G) omega).Walk (some o) (some y) :=
    p.map (SimpleGraph.Embedding.induce Set.univ).toHom
  have hnone : none ∉ q.support := by
    intro hn
    apply hnot
    refine ⟨Set.mem_univ _, none, Set.mem_univ _, rfl, ?_⟩
    exact (q.takeUntil none hn).reachable.elim fun w ↦
      ⟨w.induce Set.univ (fun _ _ ↦ Set.mem_univ _)⟩
  have htransfer : ∀ {a b : Option V}
      (w : (openSub (withGhost G) omega).Walk a b),
      none ∉ w.support →
        (openSub (withGhost G) (abgrCloseGhost omega)).Walk a b := by
    intro a b w
    induction w with
    | nil =>
        intro h
        exact .nil
    | @cons a b c hab w ih =>
        intro hnone'
        have hnonea : a ≠ none := by
          intro ha
          apply hnone'
          exact ha ▸ (SimpleGraph.Walk.cons hab w).start_mem_support
        have hnoneb : b ≠ none := by
          intro hb
          apply hnone'
          have hbmem : b ∈ (SimpleGraph.Walk.cons hab w).support := by
            rw [SimpleGraph.Walk.support_cons]
            exact List.mem_cons_of_mem _ w.start_mem_support
          exact hb ▸ hbmem
        rcases a with _ | a
        · exact False.elim (hnonea rfl)
        · rcases b with _ | b
          · exact False.elim (hnoneb rfl)
          · apply SimpleGraph.Walk.cons
            · refine ⟨hab.1, ?_⟩
              simpa using hab.2
            · apply ih
              intro hn
              apply hnone'
              rw [SimpleGraph.Walk.support_cons]
              exact List.mem_cons_of_mem _ hn
  refine ⟨Set.mem_univ _, some y, Set.mem_univ _, rfl, ?_⟩
  exact ⟨(htransfer q hnone).induce Set.univ (fun _ _ ↦ Set.mem_univ _)⟩



theorem abbl_le_l1dist_origin_of_boundary {d n : Nat} (hn : 0 < n)
    {y : Site d} (hy : y ∈ vertexBoundary d n) :
    n ≤ l1dist d (origin d) y := by
  obtain ⟨hybox, hyinner⟩ := hy
  rw [mem_box] at hybox
  rw [mem_box] at hyinner
  push_neg at hyinner
  obtain ⟨i, hi⟩ := hyinner
  have hni : n ≤ (y i).natAbs := by omega
  have hterm : (y i).natAbs = ((origin d) i - y i).natAbs := by
    simp [origin, Int.natAbs_neg]
  rw [hterm] at hni
  exact hni.trans (Finset.single_le_sum
    (fun j hj ↦ Nat.zero_le (((origin d) j - y j).natAbs))
    (Finset.mem_univ i))



theorem abbl_activeGhost_card_ge_of_boundary {d n : Nat} (hn : 0 < n)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (y : sctBox d n) (hy : (y : Site d) ∈ vertexBoundary d n)
    (hconn : abgrCloseGhost
      (abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta) ∈
        connEvent (withGhost (sctBoxGraph d n)) Set.univ
          (some (sctBoxOrigin d n)) {some y}) :
    n + 1 ≤ (abgrActiveGhost (sctBoxGraph d n)
      (sctBoxOrigin d n) eta).card := by
  let omega := abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta
  let omega0 := abgrCloseGhost omega
  let phys : ConfigSpace (Sym2 (sctBox d n)) := fun e ↦
    omega0 (Sym2.map some e)
  obtain ⟨_, z, _, hz, ⟨p⟩⟩ := hconn
  have hzy : z = some y := Set.mem_singleton_iff.mp hz
  subst z
  let q : (openSub (withGhost (sctBoxGraph d n)) omega0).Walk
      (some (sctBoxOrigin d n)) (some y) :=
    p.map (SimpleGraph.Embedding.induce Set.univ).toHom
  have hphysical : ∀ {u v : Option (sctBox d n)}
      (w : (openSub (withGhost (sctBoxGraph d n)) omega0).Walk u v)
      (a b : sctBox d n), u = some a → v = some b →
        (openSub (sctBoxGraph d n) phys).Walk a b := by
    intro u v w
    induction w with
    | @nil u =>
        intro a b hua hub
        have hab : a = b := Option.some.inj (hua.symm.trans hub)
        subst b
        exact .nil
    | @cons u v z huv tail ih =>
        intro a b hua hzb
        subst u
        rcases v with _ | v
        · have : omega0 s(some a, none) = false := by
            simp [omega0, omega]
          have htf : true = false := huv.2.symm.trans this
          exact False.elim (by simp at htf)
        · apply SimpleGraph.Walk.cons
          · refine ⟨?_, ?_⟩
            · simpa [withGhost] using huv.1
            · simpa [phys, Sym2.map_mk] using huv.2
          · exact ih v b rfl hzb
  let w := hphysical q (sctBoxOrigin d n) y rfl rfl
  let path : (openSub (sctBoxGraph d n) phys).Walk
      (sctBoxOrigin d n) y := w.toPath
  have hpath : path.IsPath := w.toPath.2
  let lift : openSub (sctBoxGraph d n) phys →g
      openSub (withGhost (sctBoxGraph d n)) omega0 :=
    { toFun := some
      map_rel' := fun {a b} hab ↦ by
        refine ⟨?_, ?_⟩
        · simpa [withGhost] using hab.1
        · simpa [phys, Sym2.map_mk] using hab.2 }
  have hsupp : path.support.toFinset ⊆
      abgrActive (G := sctBoxGraph d n) (sctBoxOrigin d n) omega := by
    intro x hx
    rw [List.mem_toFinset] at hx
    simp only [abgrActive, Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨Set.mem_univ _, some x, Set.mem_univ _, rfl, ?_⟩
    let px := path.takeUntil x hx
    exact ⟨(px.map lift).induce Set.univ (fun _ _ ↦ Set.mem_univ _)⟩
  have hcardPath : path.support.toFinset.card = path.length + 1 := by
    rw [List.toFinset_card_of_nodup hpath.support_nodup,
      SimpleGraph.Walk.length_support]
  let forget : openSub (sctBoxGraph d n) phys →g hypercubicLattice d :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab ↦ by
        simpa [sctBoxGraph] using hab.1 }
  have hlen : n ≤ path.length := by
    have hdist := abbl_le_l1dist_origin_of_boundary hn hy
    have hwalk := l1dist_le_walk_length d (path.map forget)
    simpa [path, forget, sctBoxOrigin] using hdist.trans hwalk
  have hactiveCard : path.support.toFinset.card ≤
      (abgrActive (G := sctBoxGraph d n) (sctBoxOrigin d n) omega).card :=
    Finset.card_le_card hsupp
  have hghostCard :
      (abgrActiveGhost (sctBoxGraph d n) (sctBoxOrigin d n) eta).card =
        (abgrActive (G := sctBoxGraph d n) (sctBoxOrigin d n) omega).card := by
    simp only [abgrActiveGhost, Finset.card_map]
    rw [abgrActive_merge_eq (sctBoxGraph d n) (sctBoxOrigin d n) gamma eta]
  rw [hghostCard]
  omega



def abblResidualEvent (d n : Nat) :
    Set (ConfigSpace (Sym2 (Option (sctBox d n)))) :=
  connEvent (withGhost (sctBoxGraph d n)) Set.univ
      (some (sctBoxOrigin d n)) (abbTarget d n) ∩
    (connEvent (withGhost (sctBoxGraph d n)) Set.univ
      (some (sctBoxOrigin d n)) {none})ᶜ



theorem abbl_residual_activeGhost_card {d n : Nat} (hn : 0 < n)
    (eta : {e // e ∉ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (gamma : {e // e ∈ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
    (hres : abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta ∈
      abblResidualEvent d n) :
    n + 1 ≤ (abgrActiveGhost (sctBoxGraph d n)
      (sctBoxOrigin d n) eta).card := by
  let omega := abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta
  obtain ⟨hmix, hnot⟩ := hres
  obtain ⟨_, z, _, hzTarget, hconn⟩ := hmix
  rcases hzTarget with rfl | ⟨y, hzy, hybdry⟩
  · exact False.elim (hnot ⟨Set.mem_univ _, none, Set.mem_univ _, rfl, hconn⟩)
  · subst z
    have hphys : omega ∈ connEvent (withGhost (sctBoxGraph d n))
        Set.univ (some (sctBoxOrigin d n)) {some y} :=
      ⟨Set.mem_univ _, some y, Set.mem_univ _, rfl, hconn⟩
    have hclosed := abbl_closeGhost_conn_of_not_ghost
      (sctBoxGraph d n) (sctBoxOrigin d n) y omega hphys hnot
    exact abbl_activeGhost_card_ge_of_boundary hn eta gamma y hybdry hclosed



theorem abbl_residual_prob_le {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h)
        (abblResidualEvent d n) ≤
      Real.exp (-(h * ((n + 1 : Nat) : Real))) := by
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 ≤ abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  apply abbl_residual_le_exp (sctBoxGraph d n) (abbCoupling d n)
    (sctBoxOrigin d n) beta h hJ hbeta hh (n + 1)
    (abblResidualEvent d n)
  · intro omega hres
    exact hres.2
  · intro eta gamma hres
    exact abbl_residual_activeGhost_card hn eta gamma hres



theorem abbl_abfaMag_le_abbMag_le {d n : Nat} (hn : 0 < n)
    (beta h : Real) (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h ≤ abbMag d n beta h ∧
      abbMag d n beta h ≤
        abfaMag (sctBoxGraph d n) (abbCoupling d n)
          (sctBoxOrigin d n) beta h +
            Real.exp (-(h * ((n + 1 : Nat) : Real))) := by
  let p := abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h
  let A := connEvent (withGhost (sctBoxGraph d n)) Set.univ
    (some (sctBoxOrigin d n)) (abbTarget d n)
  let B := connEvent (withGhost (sctBoxGraph d n)) Set.univ
    (some (sctBoxOrigin d n)) {none}
  let R := abblResidualEvent d n
  have hJ : ∀ e ∈ (sctBoxGraph d n).edgeFinset,
      0 ≤ abbCoupling d n e := by
    intro e he
    simp [abbCoupling]
  have hp : ∀ e, 0 ≤ p e ∧ p e ≤ 1 :=
    abfaParams_mem (sctBoxGraph d n) (abbCoupling d n) hJ
      beta h hbeta hh
  have hBA : B ⊆ A := by
    intro omega hconn
    rcases hconn with ⟨ho, z, hz, rfl, hc⟩
    exact ⟨ho, none, hz, none_mem_abbTarget d n, hc⟩
  have hAunion : A ⊆ B ∪ R := by
    intro omega hA
    by_cases hB : omega ∈ B
    · exact Or.inl hB
    · exact Or.inr ⟨hA, hB⟩
  constructor
  · change probV p B ≤ probV p A
    exact abgi_probV_mono p hp hBA
  · change probV p A ≤ probV p B + _
    calc
      probV p A ≤ probV p (B ∪ R) := abgi_probV_mono p hp hAunion
      _ ≤ probV p B + probV p R := abgi_probV_union_le p hp B R
      _ ≤ probV p B + Real.exp (-(h * ((n + 1 : Nat) : Real))) :=
        by
          simpa only [p, R] using
            add_le_add (le_refl (probV p B))
              (abbl_residual_prob_le (d := d) hn beta h hbeta hh)



theorem abbl_abfaMag_relabel {U W : Type*}
    [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]
    (G : SimpleGraph U) [DecidableRel G.Adj]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (sigma : U ≃ W)
    (hgraph : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (J : Sym2 U → Real) (K : Sym2 W → Real)
    (hcoupling : ∀ x y, G.Adj x y →
      J s(x, y) = K s(sigma x, sigma y))
    (o : U) (beta h : Real) :
    abfaMag G J o beta h = abfaMag H K (sigma o) beta h := by
  let tau : Option U ≃ Option W := sigma.optionCongr
  have htau : ∀ a b, (withGhost G).Adj a b ↔
      (withGhost H).Adj (tau a) (tau b) := by
    intro a b
    rcases a with _ | a <;> rcases b with _ | b <;>
      simp [tau, withGhost, hgraph]
  unfold abfaMag
  rw [abb_probV_connEvent_relabel (withGhost G) (withGhost H) tau htau
    (abfaParams G J beta h) (some o) none]
  congr 1
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rw [abbl_abbEdgeEquiv_symm_mk]
      rcases a with _ | a <;> rcases b with _ | b
      · change abfaParams G J beta h s(none, none) =
          abfaParams H K beta h s(none, none)
        simp [abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges, abfaLiftCoupling, abfaBaseCoupling,
          FieldGhostDict.ghostCoupling, pBeta]
      · change abfaParams G J beta h s(none, some (sigma.symm b)) =
          abfaParams H K beta h s(none, some b)
        simp [abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges]
      · change abfaParams G J beta h s(some (sigma.symm a), none) =
          abfaParams H K beta h s(some a, none)
        simp [abfaParams, abpdBetaFieldParams, paramOn,
          FieldGhostDict.ghostEdges]
      · change abfaParams G J beta h
          s(some (sigma.symm a), some (sigma.symm b)) =
            abfaParams H K beta h s(some a, some b)
        simp only [abfaParams, abpdBetaFieldParams, paramOn]
        have hghostU : s(some (sigma.symm a), some (sigma.symm b)) ∉
            FieldGhostDict.ghostEdges U := by
          simp [FieldGhostDict.ghostEdges]
        have hghostW : s(some a, some b) ∉
            FieldGhostDict.ghostEdges W := by
          simp [FieldGhostDict.ghostEdges]
        rw [if_neg hghostU, if_neg hghostW,
          abfaLiftCoupling_some_some, abfaLiftCoupling_some_some]
        by_cases hab : G.Adj (sigma.symm a) (sigma.symm b)
        · have hab' : H.Adj a b := by
            simpa using (hgraph (sigma.symm a) (sigma.symm b)).mp hab
          rw [if_pos (SimpleGraph.mem_edgeFinset.mpr hab),
            if_pos (SimpleGraph.mem_edgeFinset.mpr hab')]
          have hc : J s(sigma.symm a, sigma.symm b) = K s(a, b) := by
            simpa using hcoupling (sigma.symm a) (sigma.symm b) hab
          exact congrArg (fun t ↦ pBeta t beta) hc
        · have hab' : ¬ H.Adj a b := fun hw ↦
            hab ((hgraph (sigma.symm a) (sigma.symm b)).mpr (by simpa using hw))
          rw [if_neg (fun he ↦ hab (SimpleGraph.mem_edgeFinset.mp he)),
            if_neg (fun he ↦ hab' (SimpleGraph.mem_edgeFinset.mp he))]



noncomputable def abblLatticeCoupling (d : Nat) : Sym2 (Site d) → Real :=
  Sym2.lift ⟨fun x y ↦
    if (hypercubicLattice d).Adj x y then 1 else 0, by
      intro x y
      change (if (hypercubicLattice d).Adj x y then 1 else 0) =
        if (hypercubicLattice d).Adj y x then 1 else 0
      by_cases hxy : (hypercubicLattice d).Adj x y
      · rw [if_pos hxy, if_pos hxy.symm]
      · rw [if_neg hxy, if_neg (fun hyx ↦ hxy hyx.symm)]⟩

@[simp] theorem abblLatticeCoupling_mk (d : Nat) (x y : Site d) :
    abblLatticeCoupling d s(x, y) =
      if (hypercubicLattice d).Adj x y then 1 else 0 := by
  simp [abblLatticeCoupling]

theorem abblLatticeCoupling_nonneg (d : Nat) (e : Sym2 (Site d)) :
    0 ≤ abblLatticeCoupling d e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [abblLatticeCoupling_mk]
      split <;> norm_num

theorem abblLatticeCoupling_support {d : Nat} (x y : Site d)
    (hxy : ¬ (hypercubicLattice d).Adj x y) :
    abblLatticeCoupling d s(x, y) = 0 := by
  rw [abblLatticeCoupling_mk, if_neg hxy]



noncomputable def abblBoxEquiv (d n : Nat) :
    sctBox d n ≃ ↑(ablBoxFinset d n) where
  toFun x := ⟨x.1, mem_ablBoxFinset.mpr x.2⟩
  invFun x := ⟨x.1, mem_ablBoxFinset.mp x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

@[simp] theorem abblBoxEquiv_val (d n : Nat) (x : sctBox d n) :
    ((abblBoxEquiv d n x : ↑(ablBoxFinset d n)) : Site d) = x := rfl

@[simp] theorem abblBoxEquiv_origin (d n : Nat) :
    abblBoxEquiv d n (sctBoxOrigin d n) =
      ⟨(0 : Site d), zero_mem_ablBoxFinset d n⟩ := by
  ext i
  rfl



theorem abbl_abfaMag_eq_window (d n : Nat) (beta h : Real) :
    abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h =
      abfaMag
        (abigWindowGraph (hypercubicLattice d) (ablBoxFinset d n))
        (abigWindowCoupling (abblLatticeCoupling d) (ablBoxFinset d n))
        ⟨(0 : Site d), zero_mem_ablBoxFinset d n⟩ beta h := by
  simpa using abbl_abfaMag_relabel
    (sctBoxGraph d n)
    (abigWindowGraph (hypercubicLattice d) (ablBoxFinset d n))
    (abblBoxEquiv d n)
    (by
      intro x y
      simp [sctBoxGraph, abigWindowGraph, abblBoxEquiv])
    (abbCoupling d n)
    (abigWindowCoupling (abblLatticeCoupling d) (ablBoxFinset d n))
    (by
      intro x y hxy
      have hamb : (hypercubicLattice d).Adj (x : Site d) (y : Site d) := by
        simpa [sctBoxGraph] using hxy
      rw [abigWindowCoupling_mk, abblLatticeCoupling_mk]
      change 1 = if (hypercubicLattice d).Adj (x : Site d) (y : Site d)
        then 1 else 0
      rw [if_pos hamb])
    (sctBoxOrigin d n) beta h



theorem abbl_finiteGhost_eq_ambient {d n : Nat} (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h =
      (abigMeasure (abblLatticeCoupling d) beta h).real
        (connEvent (withGhost (hypercubicLattice d))
          (abigGhostWindow (ablBoxFinset d n) : Set (Option (Site d)))
          (some (origin d)) {none}) := by
  rw [abbl_abfaMag_eq_window]
  exact abig_abfaMag_eq_finiteConn (hypercubicLattice d)
    (abblLatticeCoupling d) (ablBoxFinset d n)
    ⟨origin d, zero_mem_ablBoxFinset d n⟩ beta h hbeta hh
    (abblLatticeCoupling_nonneg d) abblLatticeCoupling_support



theorem abbl_tendsto_finiteGhost_shiftedBase (d : Nat) (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 ≤ h) :
    Tendsto
      (fun n ↦ abfaMag (sctBoxGraph d n) (abbCoupling d n)
        (sctBoxOrigin d n) beta h)
      atTop
      (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d)
        (0 : Site d) beta h)) := by
  have hlim := abig_tendsto_abfaMag_exhaustion
    (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d)
    beta h hbeta hh
    (abblLatticeCoupling_nonneg d) abblLatticeCoupling_support
    (ablBoxFinset d) (zero_mem_ablBoxFinset d)
    (ablGhostWindow_mono d) (ablGhostWindow_cover d)
  apply hlim.congr'
  exact Filter.Eventually.of_forall fun n ↦
    (abbl_abfaMag_eq_window d n beta h).symm



theorem abbl_tendsto_boundaryError_zero (h : Real) (hh : 0 < h) :
    Tendsto
      (fun n : Nat ↦ Real.exp (-(h * (((n + 2 : Nat) : Real)))))
      atTop (nhds 0) := by
  apply Real.tendsto_exp_atBot.comp
  apply tendsto_neg_atBot_iff.mpr
  have hn : Tendsto (fun n : Nat ↦ ((n : Real) + 2)) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  simpa only [Nat.cast_add, Nat.cast_ofNat] using hn.const_mul_atTop hh




theorem abbl_tendsto_abbMag_shifted (d : Nat) (beta h : Real)
    (hbeta : 0 ≤ beta) (hh : 0 < h) :
    Tendsto (fun n ↦ abbMag d (n + 1) beta h) atTop
      (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d)
        (0 : Site d) beta h)) := by
  let M := abigMag (hypercubicLattice d) (abblLatticeCoupling d)
    (0 : Site d) beta h
  let P : Nat → Real := fun n ↦
    abfaMag (sctBoxGraph d (n + 1)) (abbCoupling d (n + 1))
      (sctBoxOrigin d (n + 1)) beta h
  let E : Nat → Real := fun n ↦
    Real.exp (-(h * (((n + 2 : Nat) : Real))))
  have hshift : Tendsto (fun n : Nat ↦ n + 1) atTop atTop :=
    (Filter.tendsto_add_atTop_iff_nat 1).2 tendsto_id
  have hP : Tendsto P atTop (nhds M) := by
    exact (abbl_tendsto_finiteGhost_shiftedBase d beta h hbeta hh.le).comp hshift
  have hE : Tendsto E atTop (nhds 0) :=
    abbl_tendsto_boundaryError_zero h hh
  have hPE : Tendsto (fun n ↦ P n + E n) atTop (nhds M) := by
    simpa [M] using hP.add hE
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hP hPE
  · intro n
    simpa [P] using
      (abbl_abfaMag_le_abbMag_le (d := d) (n := n + 1)
        (Nat.succ_pos n) beta h hbeta hh.le).1
  · intro n
    simpa [P, E, Nat.add_assoc] using
      (abbl_abfaMag_le_abbMag_le (d := d) (n := n + 1)
        (Nat.succ_pos n) beta h hbeta hh.le).2


end Sharpness
end StatMech
