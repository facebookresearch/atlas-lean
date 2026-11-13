/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FK.EdgeConfigZ
import Code.FK.EdwardsSokal
import Code.Ising.PressureBCIndep
import Code.Ising.FiniteVolumeSum
import Code.IsingFK.Q2
import Code.Sharpness.MeanfieldIsingState
import Code.Ising.PressureSurfaceVolume
import Code.FrontierA.LeeYangLogDerivativeBound

open scoped BigOperators
open Finset Filter Topology Set SimpleGraph

namespace StatMech.FrontierA

open StatMech.Ising StatMech.FK StatMech.Lattice StatMech.Sharpness



variable {V : Type*} [Fintype V] [DecidableEq V]

theorem bond_abs_le_one_general (s : ConfigSpace V) (e : Sym2 V) : |bond s e| ≤ 1 := by
  induction e using Sym2.ind with
  | _ x y =>
      rw [bond_mk, abs_mul]
      nlinarith [abs_spin_le_one s x, abs_spin_le_one s y,
        abs_nonneg (spin s x), abs_nonneg (spin s y)]


theorem isingHamiltonian_sub_abs_le_edgeDiff
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (h : ℝ) (s : ConfigSpace V) :
    |hamiltonian G h s - hamiltonian H h s| ≤ (G.edgeFinset \ H.edgeFinset).card := by
  have hsub : H.edgeFinset ⊆ G.edgeFinset := SimpleGraph.edgeFinset_mono hHG
  have hsplit :
      (∑ e ∈ G.edgeFinset, bond s e) - ∑ e ∈ H.edgeFinset, bond s e =
        ∑ e ∈ G.edgeFinset \ H.edgeFinset, bond s e := by
    rw [← Finset.sum_sdiff hsub]
    ring
  have heq : hamiltonian G h s - hamiltonian H h s =
      -((∑ e ∈ G.edgeFinset, bond s e) - ∑ e ∈ H.edgeFinset, bond s e) := by
    unfold hamiltonian
    ring
  rw [heq, abs_neg, hsplit]
  calc
    |∑ e ∈ G.edgeFinset \ H.edgeFinset, bond s e| ≤
        ∑ e ∈ G.edgeFinset \ H.edgeFinset, |bond s e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e ∈ G.edgeFinset \ H.edgeFinset, (1 : ℝ) :=
      Finset.sum_le_sum (fun e _ => bond_abs_le_one_general s e)
    _ = (G.edgeFinset \ H.edgeFinset).card := by
      rw [Finset.sum_const, nsmul_eq_mul, mul_one]


theorem isingLogZ_sub_abs_le_edgeDiff
    (G H : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel H.Adj]
    (hHG : H ≤ G) (beta h : ℝ) :
    |Real.log (isingZ G beta h) - Real.log (isingZ H beta h)| ≤
      |beta| * (G.edgeFinset \ H.edgeFinset).card := by
  exact logZ_dist_le beta (hamiltonian G h) (hamiltonian H h)
    ((G.edgeFinset \ H.edgeFinset).card)
    (isingHamiltonian_sub_abs_le_edgeDiff G H hHG h)

theorem isingSum_edgeCard
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W)
    [DecidableRel G.Adj] [DecidableRel H.Adj] :
    (G ⊕g H).edgeFinset.card = G.edgeFinset.card + H.edgeFinset.card := by
  rw [fsm_edgeFinset_sum, Finset.card_union_of_disjoint (fsm_images_disjoint G H),
    Finset.card_image_of_injective _ fsm_map_inl_injective,
    Finset.card_image_of_injective _ fsm_map_inr_injective]


theorem agl_interfaceCard_add_edgeCards
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P] :
    agl_interfaceCard G P + (agl_left G P).edgeFinset.card +
        (agl_right G P).edgeFinset.card = G.edgeFinset.card := by
  let L := agl_left G P
  let R := agl_right G P
  let K := agl_glueGraph G P
  have hsub : (L ⊕g R).edgeFinset ⊆ K.edgeFinset :=
    SimpleGraph.edgeFinset_mono (agl_partitionCrossInterface G P).le
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  have hiso := (agl_iso G P).card_edgeFinset_eq
  have hsum := isingSum_edgeCard L R
  change G.edgeFinset.card = K.edgeFinset.card at hiso
  change (K.edgeFinset \ (L ⊕g R).edgeFinset).card +
      L.edgeFinset.card + R.edgeFinset.card = G.edgeFinset.card
  omega


theorem isingLogZ_partition_sub_abs_le
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (P : V → Prop) [DecidablePred P] (beta h : ℝ) :
    |Real.log (isingZ G beta h) -
        (Real.log (isingZ (agl_left G P) beta h) +
          Real.log (isingZ (agl_right G P) beta h))| ≤
      |beta| * agl_interfaceCard G P := by
  let L := agl_left G P
  let R := agl_right G P
  let K := agl_glueGraph G P
  have hcomp := isingLogZ_sub_abs_le_edgeDiff K (L ⊕g R)
    (agl_partitionCrossInterface G P).le beta h
  have hG : isingZ G beta h = isingZ K beta h := by
    exact isingZ_relabel G K (agl_iso G P).toEquiv
      (fun x y => (agl_iso G P).map_rel_iff.symm) beta h
  have hsum : Real.log (isingZ (L ⊕g R) beta h) =
      Real.log (isingZ L beta h) + Real.log (isingZ R beta h) := by
    rw [isingZ_sum, Real.log_mul (isingZ_ne_zero L beta h) (isingZ_ne_zero R beta h)]
  simpa only [hG, hsum, agl_interfaceCard, L, R, K] using hcomp


theorem isingZ_empty {W : Type*} [Fintype W] [DecidableEq W] [IsEmpty W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (beta h : ℝ) :
    isingZ G beta h = 1 := by
  unfold isingZ
  have hs : Subsingleton (ConfigSpace W) :=
    ⟨fun a b => funext (fun x => isEmptyElim x)⟩
  have hedge : G.edgeFinset = ∅ := by
    rw [SimpleGraph.edgeFinset_eq_empty]
    ext x y
    exact ⟨fun _ => isEmptyElim x, fun hx => hx.elim⟩
  rw [Finset.sum_eq_single (fun _ => false)]
  · simp [isingWeight, hamiltonian, hedge]
  · intro b _ hb
    exact absurd (Subsingleton.elim b (fun _ => false)) hb
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

section TagPeel

variable {T : Type*} [DecidableEq T]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (tag : V → T)

theorem isingZ_left_tag (tau : T) (S : Finset T) (htau : tau ∉ S) (beta h : ℝ) :
    isingZ (agl_left (qp_restG G tag (insert tau S)) (fun x => tag x.1 = tau)) beta h =
      isingZ (qp_blkG G tag tau) beta h := by
  let phi := qp_comapComapIso G
    (Subtype.val : {x : V // tag x ∈ insert tau S} → V)
    (Subtype.val : {x : {x : V // tag x ∈ insert tau S} // tag x.1 = tau} → _)
    (Subtype.val : {x : V // tag x = tau} → V)
    (by intro a b hab; apply Subtype.ext; apply Subtype.ext; exact hab)
    Subtype.val_injective
    (by
      ext u
      constructor
      · rintro ⟨v, rfl⟩
        exact ⟨⟨v.1, v.2⟩, rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨⟨⟨v.1, by rw [v.2]; exact Finset.mem_insert_self tau S⟩, v.2⟩, rfl⟩)
  exact isingZ_relabel _ _ phi.toEquiv
    (fun x y => phi.map_rel_iff.symm) beta h

theorem isingZ_right_tag (tau : T) (S : Finset T) (htau : tau ∉ S) (beta h : ℝ) :
    isingZ (agl_right (qp_restG G tag (insert tau S)) (fun x => tag x.1 = tau)) beta h =
      isingZ (qp_restG G tag S) beta h := by
  let phi := qp_comapComapIso G
    (Subtype.val : {x : V // tag x ∈ insert tau S} → V)
    (Subtype.val : {x : {x : V // tag x ∈ insert tau S} // ¬ tag x.1 = tau} → _)
    (Subtype.val : {x : V // tag x ∈ S} → V)
    (by intro a b hab; apply Subtype.ext; apply Subtype.ext; exact hab)
    Subtype.val_injective
    (by
      ext u
      constructor
      · rintro ⟨v, rfl⟩
        have hv := v.1.2
        rw [Finset.mem_insert] at hv
        rcases hv with hv | hv
        · exact absurd hv v.2
        · exact ⟨⟨v.1.1, hv⟩, rfl⟩
      · rintro ⟨v, rfl⟩
        exact ⟨⟨⟨v.1, Finset.mem_insert_of_mem v.2⟩,
          fun hc => htau (hc ▸ v.2)⟩, rfl⟩)
  exact isingZ_relabel _ _ phi.toEquiv
    (fun x y => phi.map_rel_iff.symm) beta h


theorem isingLogZ_tagPeel (beta h : ℝ) : ∀ S : Finset T, ∃ I : ℕ,
    |Real.log (isingZ (qp_restG G tag S) beta h) -
      ∑ tau ∈ S, Real.log (isingZ (qp_blkG G tag tau) beta h)| ≤ |beta| * I ∧
    I + ∑ tau ∈ S, (qp_blkG G tag tau).edgeFinset.card =
      (qp_restG G tag S).edgeFinset.card := by
  intro S
  induction S using Finset.induction with
  | empty =>
      refine ⟨0, ?_, ?_⟩
      · haveI : IsEmpty {x : V // tag x ∈ (∅ : Finset T)} :=
          ⟨fun x => by simpa using x.2⟩
        rw [Finset.sum_empty, isingZ_empty, Real.log_one]
        simp
      · haveI : IsEmpty {x : V // tag x ∈ (∅ : Finset T)} :=
          ⟨fun x => by simpa using x.2⟩
        simp only [Finset.sum_empty, add_zero]
        have hedge : (qp_restG G tag (∅ : Finset T)).edgeFinset = ∅ := by
          rw [SimpleGraph.edgeFinset_eq_empty]
          ext x y
          exact ⟨fun _ => isEmptyElim x, fun hx => hx.elim⟩
        rw [hedge, Finset.card_empty]
  | @insert tau S htau ih =>
      obtain ⟨I0, hI0, hcard0⟩ := ih
      let R := qp_restG G tag (insert tau S)
      let P : {x : V // tag x ∈ insert tau S} → Prop := fun x => tag x.1 = tau
      let Is := agl_interfaceCard R P
      refine ⟨Is + I0, ?_, ?_⟩
      · rw [Finset.sum_insert htau]
        have hpart := isingLogZ_partition_sub_abs_le R P beta h
        rw [isingZ_left_tag G tag tau S htau,
          isingZ_right_tag G tag tau S htau] at hpart
        calc
          |Real.log (isingZ R beta h) -
              (Real.log (isingZ (qp_blkG G tag tau) beta h) +
                ∑ sigma ∈ S, Real.log (isingZ (qp_blkG G tag sigma) beta h))| =
              |(Real.log (isingZ R beta h) -
                  (Real.log (isingZ (qp_blkG G tag tau) beta h) +
                    Real.log (isingZ (qp_restG G tag S) beta h))) +
                (Real.log (isingZ (qp_restG G tag S) beta h) -
                  ∑ sigma ∈ S, Real.log (isingZ (qp_blkG G tag sigma) beta h))| := by
                congr 1 <;> ring
          _ ≤ |Real.log (isingZ R beta h) -
                  (Real.log (isingZ (qp_blkG G tag tau) beta h) +
                    Real.log (isingZ (qp_restG G tag S) beta h))| +
                |Real.log (isingZ (qp_restG G tag S) beta h) -
                  ∑ sigma ∈ S, Real.log (isingZ (qp_blkG G tag sigma) beta h)| :=
              abs_add_le _ _
          _ ≤ |beta| * Is + |beta| * I0 := add_le_add hpart hI0
          _ = |beta| * ((Is : ℝ) + (I0 : ℝ)) := by ring
          _ = |beta| * ((Is + I0 : ℕ) : ℝ) := by norm_num
      · rw [Finset.sum_insert htau]
        have hpart := agl_interfaceCard_add_edgeCards R P
        rw [ecz_left_edge_card G tag tau S htau,
          ecz_right_edge_card G tag tau S htau] at hpart
        change Is + I0 +
            ((qp_blkG G tag tau).edgeFinset.card +
              ∑ sigma ∈ S, (qp_blkG G tag sigma).edgeFinset.card) = R.edgeFinset.card
        omega

end TagPeel



theorem isingLogZ_abs_le
    (G : SimpleGraph V) [DecidableRel G.Adj] (beta h : ℝ) :
    |Real.log (isingZ G beta h)| ≤
      (Fintype.card V : ℝ) * Real.log 2 +
        |beta| * ((G.edgeFinset.card : ℝ) + |h| * Fintype.card V) := by
  let E : ConfigSpace V → ℝ := fun s => -beta * hamiltonian G h s
  let M : ℝ := |beta| * ((G.edgeFinset.card : ℝ) + |h| * Fintype.card V)
  have hE : ∀ s, |E s| ≤ M := by
    intro s
    have hb : |(∑ e ∈ G.edgeFinset, bond s e : ℝ)| ≤ G.edgeFinset.card := by
      calc
        |(∑ e ∈ G.edgeFinset, bond s e : ℝ)| ≤
            ∑ e ∈ G.edgeFinset, |bond s e| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _e ∈ G.edgeFinset, (1 : ℝ) :=
          Finset.sum_le_sum (fun e _ => bond_abs_le_one_general s e)
        _ = G.edgeFinset.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hs : |(∑ v : V, spin s v : ℝ)| ≤ Fintype.card V := by
      calc
        |(∑ v : V, spin s v : ℝ)| ≤ ∑ v : V, |spin s v| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _v : V, (1 : ℝ) :=
          Finset.sum_le_sum (fun v _ => abs_spin_le_one s v)
        _ = Fintype.card V := by simp
    unfold E M hamiltonian
    rw [abs_mul]
    have hhamm : |-((∑ e ∈ G.edgeFinset, bond s e : ℝ)) -
        h * ∑ v : V, spin s v| ≤
        (G.edgeFinset.card : ℝ) + |h| * Fintype.card V := by
      calc
        |-((∑ e ∈ G.edgeFinset, bond s e : ℝ)) - h * ∑ v : V, spin s v| ≤
            |(∑ e ∈ G.edgeFinset, bond s e : ℝ)| +
              |h| * |(∑ v : V, spin s v : ℝ)| := by
                simpa [abs_mul] using abs_add_le
                  (-(∑ e ∈ G.edgeFinset, bond s e : ℝ))
                  (-h * ∑ v : V, spin s v)
        _ ≤ (G.edgeFinset.card : ℝ) + |h| * Fintype.card V := by
          gcongr
    rw [abs_neg]
    exact mul_le_mul_of_nonneg_left hhamm (abs_nonneg beta)
  have hlow : Real.exp (-M) * Fintype.card (ConfigSpace V) ≤ isingZ G beta h := by
    change Real.exp (-M) * Fintype.card (ConfigSpace V) ≤ ∑ s, Real.exp (E s)
    calc
      Real.exp (-M) * Fintype.card (ConfigSpace V) =
          ∑ _s : ConfigSpace V, Real.exp (-M) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
            ring
      _ ≤ ∑ s, Real.exp (E s) := Finset.sum_le_sum (fun s _ =>
        Real.exp_le_exp.mpr (neg_le_of_abs_le (hE s)))
  have hupp : isingZ G beta h ≤ Real.exp M * Fintype.card (ConfigSpace V) := by
    change (∑ s, Real.exp (E s)) ≤ Real.exp M * Fintype.card (ConfigSpace V)
    calc
      (∑ s, Real.exp (E s)) ≤ ∑ _s : ConfigSpace V, Real.exp M :=
        Finset.sum_le_sum (fun s _ => Real.exp_le_exp.mpr (le_of_abs_le (hE s)))
      _ = Real.exp M * Fintype.card (ConfigSpace V) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        ring
  have hcard : (Fintype.card (ConfigSpace V) : ℝ) = 2 ^ Fintype.card V := by
    simp [ConfigSpace, Fintype.card_bool]
  have hloglow := Real.log_le_log (mul_pos (Real.exp_pos _) (by positivity)) hlow
  have hlogupp := Real.log_le_log (isingZ_pos G beta h) hupp
  rw [Real.log_mul (Real.exp_ne_zero _) (by positivity), Real.log_exp,
    hcard, Real.log_pow] at hloglow hlogupp
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hVlog : 0 ≤ (Fintype.card V : ℝ) * Real.log 2 :=
    mul_nonneg (Nat.cast_nonneg _) hlog2
  change |Real.log (isingZ G beta h)| ≤
    (Fintype.card V : ℝ) * Real.log 2 + M
  rw [abs_le]
  constructor <;> linarith



noncomputable def isingBoxLogZ (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  Real.log (isingZ (boxGraph d n) beta h)

noncomputable def isingBoxPressureSeq (d : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  isingBoxLogZ d beta h n / (Fintype.card (boxVerts d n) : ℝ)

theorem ising_vanHove_none_vertex_card (d m n : ℕ) :
    Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = none} +
        (ecz_T m n) ^ d * Fintype.card (boxVerts d m) = Fintype.card (boxVerts d n) := by
  have htotal : Fintype.card (boxVerts d n) =
      ∑ tau : Option (Fin d → Fin (ecz_T m n)),
        Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = tau} := by
    calc
      Fintype.card (boxVerts d n) =
          Fintype.card ((tau : Option (Fin d → Fin (ecz_T m n))) ×
            {x : boxVerts d n // ecz_vanHoveTag m n x = tau}) :=
        Fintype.card_congr (Equiv.sigmaFiberEquiv (ecz_vanHoveTag m n)).symm
      _ = _ := Fintype.card_sigma
  rw [Fintype.sum_option] at htotal
  have heach : ∀ c : Fin d → Fin (ecz_T m n),
      Fintype.card {x : boxVerts d n // ecz_vanHoveTag m n x = some c} =
        Fintype.card (boxVerts d m) := fun c =>
    (Fintype.card_congr (ecz_cellEquiv m n c)).symm
  rw [Finset.sum_congr rfl (fun c _ => heach c), Finset.sum_const,
    Finset.card_univ, ecz_cell_card, nsmul_eq_mul] at htotal
  exact htotal.symm

theorem isingZ_cellBlock (d m n : ℕ) (c : Fin d → Fin (ecz_T m n))
    (beta h : ℝ) :
    isingZ (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c)) beta h =
      isingZ (boxGraph d m) beta h := by
  exact (isingZ_relabel (boxGraph d m)
    (qp_blkG (boxGraph d n) (ecz_vanHoveTag m n) (some c))
    (ecz_cellBlockIso m n c).toEquiv
    (fun x y => (ecz_cellBlockIso m n c).map_rel_iff.symm) beta h).symm


theorem isingBoxLogZ_vanHove_abs_le (d m n : ℕ) (beta h : ℝ) :
    |isingBoxLogZ d beta h n - ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤
      (Real.log 2 + |beta| * |h|) *
          ((Fintype.card (boxVerts d n) : ℝ) -
            ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) +
        |beta| * (((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card) := by
  classical
  let tag : boxVerts d n → Option (Fin d → Fin (ecz_T m n)) :=
    ecz_vanHoveTag (d := d) m n
  obtain ⟨I, hpeel, hcard⟩ :=
    isingLogZ_tagPeel (boxGraph d n) tag beta h Finset.univ
  have hrest : isingZ (qp_restG (boxGraph d n) tag Finset.univ) beta h =
      isingZ (boxGraph d n) beta h := by
    exact isingZ_relabel _ _ (ecz_restUnivIso m n).toEquiv
      (fun x y => (ecz_restUnivIso m n).map_rel_iff.symm) beta h
  let N := qp_blkG (boxGraph d n) tag none
  have hsumZ : (∑ tau ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
      Real.log (isingZ (qp_blkG (boxGraph d n) tag tau) beta h)) =
      Real.log (isingZ N beta h) +
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m := by
    rw [show (∑ tau ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        Real.log (isingZ (qp_blkG (boxGraph d n) tag tau) beta h)) =
      ∑ tau : Option (Fin d → Fin (ecz_T m n)),
        Real.log (isingZ (qp_blkG (boxGraph d n) tag tau) beta h) from rfl,
      Fintype.sum_option]
    congr 1
    rw [Finset.sum_congr rfl (fun c _ => by rw [isingZ_cellBlock d m n c]),
      Finset.sum_const, Finset.card_univ, ecz_cell_card, nsmul_eq_mul]
    push_cast
    rfl
  have hsumE : I + N.edgeFinset.card +
      (ecz_T m n) ^ d * (boxGraph d m).edgeFinset.card =
        (boxGraph d n).edgeFinset.card := by
    rw [show (∑ tau ∈ (Finset.univ : Finset (Option (Fin d → Fin (ecz_T m n)))),
        (qp_blkG (boxGraph d n) tag tau).edgeFinset.card) =
      ∑ tau : Option (Fin d → Fin (ecz_T m n)),
        (qp_blkG (boxGraph d n) tag tau).edgeFinset.card from rfl,
      Fintype.sum_option] at hcard
    rw [Finset.sum_congr rfl (fun c _ => ecz_cellBlock_edge_card m n c),
      Finset.sum_const, Finset.card_univ, ecz_cell_card, nsmul_eq_mul] at hcard
    have hrestE := (ecz_restUnivIso (d := d) m n).card_edgeFinset_eq
    change (qp_restG (boxGraph d n) tag Finset.univ).edgeFinset.card =
      (boxGraph d n).edgeFinset.card at hrestE
    simpa [tag, N, hrestE, Nat.add_assoc] using hcard
  let VN := Fintype.card {x : boxVerts d n // tag x = none}
  have hsumV : VN + (ecz_T m n) ^ d * Fintype.card (boxVerts d m) =
      Fintype.card (boxVerts d n) := by
    simpa [tag, VN] using ising_vanHove_none_vertex_card d m n
  have hNbound := isingLogZ_abs_le N beta h
  rw [hrest, hsumZ] at hpeel
  change |isingBoxLogZ d beta h n -
      (Real.log (isingZ N beta h) +
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m)| ≤ |beta| * I at hpeel
  have htri : |isingBoxLogZ d beta h n -
      ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤
      |beta| * I + |Real.log (isingZ N beta h)| := by
    calc
      |isingBoxLogZ d beta h n -
          ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| =
          |(isingBoxLogZ d beta h n -
              (Real.log (isingZ N beta h) +
                ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m)) +
            Real.log (isingZ N beta h)| := by congr 1 <;> ring
      _ ≤ |isingBoxLogZ d beta h n -
              (Real.log (isingZ N beta h) +
                ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m)| +
            |Real.log (isingZ N beta h)| := abs_add_le _ _
      _ ≤ |beta| * I + |Real.log (isingZ N beta h)| := by
        simpa using add_le_add_right hpeel |Real.log (isingZ N beta h)|
  have hVN : Fintype.card {x : boxVerts d n // tag x = none} = VN := rfl
  change |Real.log (isingZ N beta h)| ≤
    (VN : ℝ) * Real.log 2 +
      |beta| * ((N.edgeFinset.card : ℝ) + |h| * VN) at hNbound
  have hsumER : (I : ℝ) + (N.edgeFinset.card : ℝ) +
      ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) =
        ((boxGraph d n).edgeFinset.card : ℝ) := by exact_mod_cast hsumE
  have hsumVR : (VN : ℝ) + ((ecz_T m n) ^ d : ℝ) *
      (Fintype.card (boxVerts d m) : ℝ) =
        (Fintype.card (boxVerts d n) : ℝ) := by exact_mod_cast hsumV
  calc
    |isingBoxLogZ d beta h n -
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| ≤
        |beta| * I + |Real.log (isingZ N beta h)| := htri
    _ ≤ |beta| * I + ((VN : ℝ) * Real.log 2 +
      |beta| * ((N.edgeFinset.card : ℝ) + |h| * VN)) :=
        by simpa using add_le_add_left hNbound (|beta| * (I : ℝ))
    _ = (Real.log 2 + |beta| * |h|) *
          ((Fintype.card (boxVerts d n) : ℝ) -
            ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) +
        |beta| * (((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card) := by
      rw [← hsumVR, ← hsumER]
      ring



theorem isingBox_vertexBulkFraction_tendsto (d m : ℕ) :
    Tendsto (fun n =>
      ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds 1) := by
  have h := (ecz_packing_ratio_tendsto m).pow d
  convert h using 1
  · funext n
    rw [ecz_boxVerts_card, ecz_boxVerts_card]
    push_cast
    rw [div_pow, mul_pow]
  · simp

theorem isingBox_edge_div_vertex_eq (d n : ℕ) (hd : 1 ≤ d) :
    ((boxGraph d n).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ) =
      (d : ℝ) * (2 * (n : ℝ)) / (2 * n + 1) := by
  rw [EdgeCount.boxGraph_edgeCard d n hd, ecz_boxVerts_card]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  push_cast
  have hside : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  rw [pow_succ]
  field_simp

theorem isingBox_edgeDensity_tendsto (d : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n => ((boxGraph d n).edgeFinset.card : ℝ) /
      (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds (d : ℝ)) := by
  have hden : Tendsto (fun n : ℕ => 2 * (n : ℝ) + 1) atTop atTop :=
    ecz_denom_tendsto_atTop
  have hzero : Tendsto (fun n : ℕ => (1 : ℝ) / (2 * n + 1)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hratio : Tendsto (fun n : ℕ => (2 * (n : ℝ)) / (2 * n + 1))
      atTop (nhds 1) := by
    have h := hzero.const_sub 1
    convert h using 1
    · funext n
      have hn : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
      field_simp
      ring
    · simp
  have hmul := (tendsto_const_nhds (x := (d : ℝ))).mul hratio
  convert hmul using 1
  · funext n
    rw [isingBox_edge_div_vertex_eq d n hd]
    ring
  · simp

theorem isingBox_bulkEdgeDensity_tendsto (d m : ℕ) :
    Tendsto (fun n =>
      ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ)) atTop
      (nhds (((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ))) := by
  have hVpos : (0 : ℝ) < Fintype.card (boxVerts d m) := by
    rw [ecz_boxVerts_card]
    positivity
  have h := (isingBox_vertexBulkFraction_tendsto d m).mul
    (tendsto_const_nhds (x := ((boxGraph d m).edgeFinset.card : ℝ) /
      (Fintype.card (boxVerts d m) : ℝ)))
  convert h using 1
  · funext n
    field_simp [ne_of_gt hVpos]
  · field_simp [ne_of_gt hVpos]

theorem isingBox_edgeDeficitDensity_tendsto (d m : ℕ) (hd : 1 ≤ d) :
    Tendsto (fun n =>
      (((boxGraph d n).edgeFinset.card : ℝ) -
        ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
          (Fintype.card (boxVerts d n) : ℝ)) atTop
      (nhds ((d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ))) := by
  have h := (isingBox_edgeDensity_tendsto d hd).sub
    (isingBox_bulkEdgeDensity_tendsto d m)
  convert h using 1
  funext n
  rw [sub_div]

theorem isingBox_edgeSurface_eq (d m : ℕ) (hd : 1 ≤ d) :
    (d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ) =
      (d : ℝ) / (2 * (m : ℝ) + 1) := by
  rw [isingBox_edge_div_vertex_eq d m hd]
  have hm : (2 * (m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

theorem isingBox_edgeSurface_tendsto_zero (d : ℕ) :
    Tendsto (fun m : ℕ => (d : ℝ) / (2 * (m : ℝ) + 1)) atTop (nhds 0) :=
  tendsto_const_nhds.div_atTop ecz_denom_tendsto_atTop



theorem isingBoxPressure_vanHove_abs_le (d m n : ℕ) (beta h : ℝ) :
    |isingBoxPressureSeq d beta h n -
        (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
          (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m| ≤
      (Real.log 2 + |beta| * |h|) *
        (1 - ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
          (Fintype.card (boxVerts d n) : ℝ)) +
      |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
        ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
          (Fintype.card (boxVerts d n) : ℝ)) := by
  have hraw := isingBoxLogZ_vanHove_abs_le d m n beta h
  have hVn : (0 : ℝ) < Fintype.card (boxVerts d n) := by
    rw [ecz_boxVerts_card]
    positivity
  have hVm : (0 : ℝ) < Fintype.card (boxVerts d m) := by
    rw [ecz_boxVerts_card]
    positivity
  have hdiv := (div_le_div_iff_of_pos_right hVn).2 hraw
  have heq : isingBoxPressureSeq d beta h n -
      (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
        (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m =
      (isingBoxLogZ d beta h n -
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m) /
          (Fintype.card (boxVerts d n) : ℝ) := by
    unfold isingBoxPressureSeq
    field_simp [ne_of_gt hVn, ne_of_gt hVm]
  calc
    |isingBoxPressureSeq d beta h n -
        (((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
          (Fintype.card (boxVerts d n) : ℝ)) * isingBoxPressureSeq d beta h m| =
      |isingBoxLogZ d beta h n -
        ((ecz_T m n) ^ d : ℝ) * isingBoxLogZ d beta h m| /
          (Fintype.card (boxVerts d n) : ℝ) := by
            rw [heq, abs_div, abs_of_pos hVn]
    _ ≤ ((Real.log 2 + |beta| * |h|) *
          ((Fintype.card (boxVerts d n) : ℝ) -
            ((ecz_T m n) ^ d : ℝ) * Fintype.card (boxVerts d m)) +
        |beta| * (((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * (boxGraph d m).edgeFinset.card)) /
            (Fintype.card (boxVerts d n) : ℝ) := hdiv
    _ = _ := by
      field_simp [ne_of_gt hVn]

private noncomputable def isingBoxCauchyBound
    (d m : ℕ) (beta h : ℝ) (n : ℕ) : ℝ :=
  let r := ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
    (Fintype.card (boxVerts d n) : ℝ)
  (Real.log 2 + |beta| * |h|) * (1 - r) +
    |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
      ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
        (Fintype.card (boxVerts d n) : ℝ)) +
    |1 - r| * |isingBoxPressureSeq d beta h m|

private theorem isingBoxPressure_sub_reference_le
    (d m n : ℕ) (beta h : ℝ) :
    |isingBoxPressureSeq d beta h n - isingBoxPressureSeq d beta h m| ≤
      isingBoxCauchyBound d m beta h n := by
  let r := ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
    (Fintype.card (boxVerts d n) : ℝ)
  have hvh := isingBoxPressure_vanHove_abs_le d m n beta h
  change |isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m| ≤
    (Real.log 2 + |beta| * |h|) * (1 - r) +
      |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
        ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
          (Fintype.card (boxVerts d n) : ℝ)) at hvh
  calc
    |isingBoxPressureSeq d beta h n - isingBoxPressureSeq d beta h m| =
        |(isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m) +
          (r - 1) * isingBoxPressureSeq d beta h m| := by congr 1 <;> ring
    _ ≤ |isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m| +
        |r - 1| * |isingBoxPressureSeq d beta h m| := by
          simpa [abs_mul] using abs_add_le
            (isingBoxPressureSeq d beta h n - r * isingBoxPressureSeq d beta h m)
            ((r - 1) * isingBoxPressureSeq d beta h m)
    _ ≤ (Real.log 2 + |beta| * |h|) * (1 - r) +
        |beta| * ((((boxGraph d n).edgeFinset.card : ℝ) -
          ((ecz_T m n) ^ d : ℝ) * ((boxGraph d m).edgeFinset.card : ℝ)) /
            (Fintype.card (boxVerts d n) : ℝ)) +
          |r - 1| * |isingBoxPressureSeq d beta h m| := by
            exact add_le_add hvh (le_refl _)
    _ = isingBoxCauchyBound d m beta h n := by
      simp only [isingBoxCauchyBound, r]
      rw [abs_sub_comm]

private theorem isingBoxCauchyBound_tendsto
    (d m : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    Tendsto (isingBoxCauchyBound d m beta h) atTop
      (nhds (|beta| * ((d : ℝ) - ((boxGraph d m).edgeFinset.card : ℝ) /
        (Fintype.card (boxVerts d m) : ℝ)))) := by
  let r : ℕ → ℝ := fun n =>
    ((ecz_T m n) ^ d : ℝ) * (Fintype.card (boxVerts d m) : ℝ) /
      (Fintype.card (boxVerts d n) : ℝ)
  have hr : Tendsto r atTop (nhds 1) := isingBox_vertexBulkFraction_tendsto d m
  have hfirst : Tendsto (fun n =>
      (Real.log 2 + |beta| * |h|) * (1 - r n)) atTop (nhds 0) := by
    convert tendsto_const_nhds.mul (tendsto_const_nhds.sub hr) using 1 <;> ring
  have hedge := (tendsto_const_nhds (x := |beta|)).mul
    (isingBox_edgeDeficitDensity_tendsto d m hd)
  have hlast : Tendsto (fun n => |1 - r n| * |isingBoxPressureSeq d beta h m|)
      atTop (nhds 0) := by
    have habs : Tendsto (fun n => |1 - r n|) atTop (nhds 0) := by
      convert (tendsto_const_nhds.sub hr).abs using 1 <;> simp
    convert habs.mul_const |isingBoxPressureSeq d beta h m| using 1 <;> ring
  have hall := (hfirst.add hedge).add hlast
  simpa only [isingBoxCauchyBound, r, zero_add, add_zero] using hall


theorem isingBoxPressure_tendsto (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ, Tendsto (isingBoxPressureSeq d beta h) atTop (nhds pressure) := by
  have hsurface : Tendsto (fun m : ℕ =>
      |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1))) atTop (nhds 0) :=
    by simpa using
      (tendsto_const_nhds (x := |beta|)).mul (isingBox_edgeSurface_tendsto_zero d)
  have hcauchy : CauchySeq (isingBoxPressureSeq d beta h) := by
    rw [Metric.cauchySeq_iff]
    intro epsilon hepsilon
    obtain ⟨m, hm⟩ := (Metric.tendsto_atTop.mp hsurface) (epsilon / 4) (by positivity)
    have hmm := hm m le_rfl
    have hsurf_nonneg : 0 ≤ |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1)) := by positivity
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hsurf_nonneg] at hmm
    have hboundlim := isingBoxCauchyBound_tendsto d m hd beta h
    rw [isingBox_edgeSurface_eq d m hd] at hboundlim
    obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.mp hboundlim) (epsilon / 4) (by positivity)
    refine ⟨N, fun a ha b hb => ?_⟩
    have hBa := hN a ha
    have hBb := hN b hb
    rw [Real.dist_eq] at hBa hBb ⊢
    have hBa' : isingBoxCauchyBound d m beta h a < epsilon / 2 := by
      have := le_abs_self (isingBoxCauchyBound d m beta h a -
        |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1)))
      linarith
    have hBb' : isingBoxCauchyBound d m beta h b < epsilon / 2 := by
      have := le_abs_self (isingBoxCauchyBound d m beta h b -
        |beta| * ((d : ℝ) / (2 * (m : ℝ) + 1)))
      linarith
    calc
      |isingBoxPressureSeq d beta h a - isingBoxPressureSeq d beta h b| =
          |(isingBoxPressureSeq d beta h a - isingBoxPressureSeq d beta h m) -
            (isingBoxPressureSeq d beta h b - isingBoxPressureSeq d beta h m)| := by
              congr 1 <;> ring
      _ ≤ |isingBoxPressureSeq d beta h a - isingBoxPressureSeq d beta h m| +
          |isingBoxPressureSeq d beta h b - isingBoxPressureSeq d beta h m| :=
            abs_sub _ _
      _ ≤ isingBoxCauchyBound d m beta h a + isingBoxCauchyBound d m beta h b :=
        add_le_add (isingBoxPressure_sub_reference_le d m a beta h)
          (isingBoxPressure_sub_reference_le d m b beta h)
      _ < epsilon / 2 + epsilon / 2 := add_lt_add hBa' hBb'
      _ = epsilon := by ring
  exact cauchySeq_tendsto_of_complete hcauchy





theorem isingZ_zeroField_eq_exp_mul_fkZEdge
    {W : Type*} [Fintype W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (beta : ℝ) :
    isingZ G beta 0 = Real.exp (beta * G.edgeFinset.card) *
      ecz_fkZEdge G (1 - Real.exp (-2 * beta)) 2 := by
  let p : ℝ := 1 - Real.exp (-2 * beta)
  have hES : fkZ G p 2 =
      esFirstConst G (2 * beta) 1 * Potts.pottsZ G 2 (2 * beta) 1 := by
    calc
      fkZ G p 2 = esZ G 2 p := (esZ_eq_fkZ G 2 p).symm
      _ = esFirstConst G (2 * beta) 1 * Potts.pottsZ G 2 (2 * beta) 1 := by
        simpa [p] using esZ_eq_pottsZ G 2 (2 * beta) 1
  rw [ecz_factorization, esFirstConst, ecz_NE_eq] at hES
  have htwo : (2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) ≠ 0 :=
    pow_ne_zero _ (by norm_num)
  have hedge : ecz_fkZEdge G p 2 =
      Real.exp (-(2 * beta * 1)) ^ G.edgeFinset.card *
        Potts.pottsZ G 2 (2 * beta) 1 := by
    apply mul_left_cancel₀ htwo
    calc
      (2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) * ecz_fkZEdge G p 2 =
          ((2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) *
            Real.exp (-(2 * beta * 1)) ^ G.edgeFinset.card) *
              Potts.pottsZ G 2 (2 * beta) 1 := hES
      _ = (2 : ℝ) ^ (Fintype.card (Sym2 W) - G.edgeFinset.card) *
          (Real.exp (-(2 * beta * 1)) ^ G.edgeFinset.card *
            Potts.pottsZ G 2 (2 * beta) 1) := by ring
  have hIsing := IsingFK.isingZ_eq G beta (2 * beta) 1 (by ring)
  rw [hIsing, hedge]
  rw [← Real.exp_nat_mul]
  rw [← mul_assoc, ← Real.exp_add]
  congr 1
  ring



theorem isingBoxLogZ_zeroField_eq_fk (d n : ℕ) {beta : ℝ} (hbeta : 0 < beta) :
    isingBoxLogZ d beta 0 n =
      beta * ((boxGraph d n).edgeFinset.card : ℝ) -
        ecz_u d (fsc_logit (1 - Real.exp (-2 * beta))) n := by
  let p : ℝ := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    rw [sub_pos, Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  rw [isingBoxLogZ, isingZ_zeroField_eq_exp_mul_fkZEdge]
  rw [Real.log_mul (Real.exp_ne_zero _)
    (ecz_fkZEdge_ne_zero (boxGraph d n) hp hp1 (by norm_num)), Real.log_exp]
  unfold ecz_u
  rw [fsc_logistic_logit hp hp1]
  change beta * ((boxGraph d n).edgeFinset.card : ℝ) +
      Real.log (ecz_fkZEdge (boxGraph d n) p 2) =
    beta * ((boxGraph d n).edgeFinset.card : ℝ) -
      -Real.log (ecz_fkZEdge (boxGraph d n) p 2)
  ring


theorem sctBoxGraph_pressure_tendsto (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ,
      Tendsto (fun n =>
        Real.log (isingZ (sctBoxGraph d n) beta h) /
          (Fintype.card (sctBox d n) : ℝ)) atTop (nhds pressure) := by
  obtain ⟨pressure, hp⟩ := isingBoxPressure_tendsto d hd beta h
  refine ⟨pressure, hp.congr' ?_⟩
  filter_upwards with n
  unfold isingBoxPressureSeq isingBoxLogZ
  let phi : boxGraph d n ≃g sctBoxGraph d n :=
    { toEquiv := Equiv.refl (boxVerts d n)
      map_rel_iff' := by
        intro x y
        change (hypercubicLattice d).Adj (x : Site d) (y : Site d) ↔
          (hypercubicLattice d).Adj (x : Site d) (y : Site d)
        rfl }
  have hZ : isingZ (boxGraph d n) beta h = isingZ (sctBoxGraph d n) beta h :=
    isingZ_relabel _ _ phi.toEquiv (fun x y => phi.map_rel_iff.symm) beta h
  rw [hZ]


theorem freeBox_fvZ_pressure_tendsto (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ,
      Tendsto (fun n =>
        Real.log (fvZ (minusField d) n (bondFinsetInternal d n) beta h) /
          ((boxFinset d n).card : ℝ)) atTop (nhds pressure) := by
  obtain ⟨pressure, hp⟩ := sctBoxGraph_pressure_tendsto d hd beta h
  refine ⟨pressure, hp.congr' ?_⟩
  filter_upwards with n
  rw [sct_fvZ_eq_isingZ, psv_volume_card, ecz_boxVerts_card]


theorem leeYangComplexFieldPartition_real_pressure_tendsto
    (d : ℕ) (hd : 1 ≤ d) (beta h : ℝ) :
    ∃ pressure : ℝ,
      Tendsto (fun n =>
        Real.log (leeYangComplexFieldPartition (boxGraph d n) beta (h : ℂ)).re /
          (Fintype.card (boxVerts d n) : ℝ)) atTop (nhds pressure) := by
  obtain ⟨pressure, hp⟩ := isingBoxPressure_tendsto d hd beta h
  refine ⟨pressure, hp.congr' ?_⟩
  filter_upwards with n
  simp only [isingBoxPressureSeq, isingBoxLogZ,
    leeYangComplexFieldPartition_ofReal, Complex.ofReal_re]




theorem leeYangBox_pressure_and_logDerivative_analytic
    (d : ℕ) (hd : 1 ≤ d) (beta : ℝ) (hbeta : 0 ≤ beta) (h : ℝ) :
    (∃ pressure : ℝ, Tendsto (isingBoxPressureSeq d beta h) atTop (nhds pressure)) ∧
      ∀ n, AnalyticOnNhd ℂ
        (leeYangNormalizedFieldLogDerivative (boxGraph d n) beta)
        {z : ℂ | z.re ≠ 0} := by
  exact ⟨isingBoxPressure_tendsto d hd beta h,
    fun n => leeYangNormalizedFieldLogDerivative_analyticOnNhd_re_ne_zero
      (boxGraph d n) hbeta⟩

end StatMech.FrontierA
