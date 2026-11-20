/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.Probability.InhomogeneousProduct
import Code.Sharpness.ABGhostRegularity
import Code.Sharpness.ABThermodynamicPassage

open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal

namespace StatMech
namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}



theorem inhom_real_eq_probV_of_mem {E : Type*} [Fintype E] [DecidableEq E]
    (r : E -> Real) (hr0 : forall e, 0 <= r e)
    (hr1 : forall e, r e <= 1) (A : Set (ConfigSpace E)) :
    (inhomBernoulliProductMeasure (fun e => (r e).toNNReal)
      (fun e => Real.toNNReal_le_one.mpr (hr1 e))).real A = probV r A := by
  rw [inhom_real_eq_wprob]
  unfold wprob probV pweight configWeightV edgeWeightV
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  apply Finset.prod_congr rfl
  intro e _
  by_cases he : omega e
  · simp only [he, if_true]
    rw [Measure.real, bernoulliMeasure_apply_true, ENNReal.coe_toReal,
      Real.coe_toNNReal _ (hr0 e)]
  · simp only [he]
    rw [Measure.real, bernoulliMeasure_apply_false, ENNReal.coe_toReal,
      NNReal.coe_sub (Real.toNNReal_le_one.mpr (hr1 e)),
      Real.coe_toNNReal _ (hr0 e)]
    norm_num



theorem inhom_map_cfgEquiv {E : Type*} (p : E -> NNReal)
    (hp : forall e, p e <= 1) (sigma : E ≃ E)
    (hinv : forall e, p (sigma e) = p e) :
    Measure.map (cfgEquiv sigma) (inhomBernoulliProductMeasure p hp) =
      inhomBernoulliProductMeasure p hp := by
  unfold inhomBernoulliProductMeasure
  have hcfg : (cfgEquiv sigma : ConfigSpace E -> ConfigSpace E) =
      (Equiv.piCongrLeft (fun _ : E => Bool) sigma.symm :
        ConfigSpace E -> ConfigSpace E) := by
    funext omega e
    simp only [cfgEquiv_apply, Equiv.piCongrLeft_apply, eq_rec_constant,
      Equiv.symm_symm]
  rw [hcfg]
  have hfamily : (fun e => bernoulliMeasure (p e) (hp e)) =
      (fun e => bernoulliMeasure (p (sigma.symm e)) (hp (sigma.symm e))) := by
    funext e
    exact bernoulliMeasure_congr _ _ (by
      simpa using hinv (sigma.symm e))
  conv_lhs => enter [2]; rw [hfamily]
  simpa only [MeasurableEquiv.coe_piCongrLeft] using
    (Measure.infinitePi_map_piCongrLeft
      (fun e => bernoulliMeasure (p e) (hp e)) sigma.symm)


theorem measurable_cfgEquiv {E F : Type*} (sigma : E ≃ F) :
    Measurable (cfgEquiv sigma : ConfigSpace F -> ConfigSpace E) := by
  have hcfg : (cfgEquiv sigma : ConfigSpace F -> ConfigSpace E) =
      (Equiv.piCongrLeft (fun _ : E => Bool) sigma.symm :
        ConfigSpace F -> ConfigSpace E) := by
    funext omega e
    simp only [cfgEquiv_apply, Equiv.piCongrLeft_apply, eq_rec_constant,
      Equiv.symm_symm]
  rw [hcfg]
  exact (MeasurableEquiv.piCongrLeft (fun _ : E => Bool) sigma.symm).measurable


noncomputable def abigRealParam (J : Sym2 V -> Real) (beta h : Real) :
    Sym2 (Option V) -> Real :=
  FieldGhostDict.ghostCoupling (qField h) 1
    (fun e => pBeta (J e) beta)

@[simp] theorem abigRealParam_some_some (J : Sym2 V -> Real)
    (beta h : Real) (x y : V) :
    abigRealParam J beta h s(some x, some y) = pBeta (J s(x, y)) beta :=
  rfl

@[simp] theorem abigRealParam_some_none (J : Sym2 V -> Real)
    (beta h : Real) (x : V) :
    abigRealParam J beta h s(some x, none) = qField h :=
  rfl


theorem abigRealParam_mem (J : Sym2 V -> Real) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e) :
    forall e, 0 <= abigRealParam J beta h e ∧
      abigRealParam J beta h e <= 1 := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abigRealParam, FieldGhostDict.ghostCoupling]
      · simpa [abigRealParam, FieldGhostDict.ghostCoupling] using qField_mem h hh
      · simpa [abigRealParam, FieldGhostDict.ghostCoupling] using qField_mem h hh
      · constructor
        · simpa [abigRealParam, FieldGhostDict.ghostCoupling] using
            pBeta_nonneg (mul_nonneg hbeta (hJ s(x, y)))
        · exact (pBeta_lt_one (J s(x, y)) beta).le




noncomputable def abigParam (J : Sym2 V -> Real) (beta h : Real) :
    Sym2 (Option V) -> NNReal :=
  fun e => (abigRealParam J beta h e).toNNReal

theorem qField_toNNReal_le_one (h : Real) : (qField h).toNNReal <= 1 := by
  rw [Real.toNNReal_le_one]
  unfold qField
  linarith [Real.exp_pos (-h)]


theorem abigParam_le_one (J : Sym2 V -> Real) (beta h : Real) :
    forall e, abigParam J beta h e <= 1 := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abigParam, abigRealParam, FieldGhostDict.ghostCoupling]
      · simpa [abigParam, abigRealParam, FieldGhostDict.ghostCoupling] using
          qField_toNNReal_le_one h
      · simpa [abigParam, abigRealParam, FieldGhostDict.ghostCoupling] using
          qField_toNNReal_le_one h
      · simpa [abigParam, abigRealParam, FieldGhostDict.ghostCoupling] using
          pBeta_toNNReal_le_one (J s(x, y)) beta

@[simp] theorem abigParam_some_some (J : Sym2 V -> Real)
    (beta h : Real) (x y : V) :
    abigParam J beta h s(some x, some y) =
      (pBeta (J s(x, y)) beta).toNNReal :=
  rfl

@[simp] theorem abigParam_some_none (J : Sym2 V -> Real)
    (beta h : Real) (x : V) :
    abigParam J beta h s(some x, none) = (qField h).toNNReal :=
  rfl



theorem abigParam_invariant (J : Sym2 V -> Real) (beta h : Real)
    (sigma : V ≃ V)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y))
    (e : Sym2 (Option V)) :
    abigParam J beta h (abfsEdgeEquiv sigma e) = abigParam J beta h e := by
  apply congrArg Real.toNNReal
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk]
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk]
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk,
          Sym2.eq_swap]
      · simp [abigRealParam, FieldGhostDict.ghostCoupling,
          abfsEdgeEquiv_mk, hJ]



noncomputable def abigMeasure (J : Sym2 V -> Real) (beta h : Real) :
    Measure (ConfigSpace (Sym2 (Option V))) :=
  inhomBernoulliProductMeasure (abigParam J beta h)
    (abigParam_le_one J beta h)

instance abigMeasure_isProbabilityMeasure (J : Sym2 V -> Real) (beta h : Real) :
    IsProbabilityMeasure (abigMeasure J beta h) := by
  unfold abigMeasure
  infer_instance



theorem abig_map_cfgEquiv (J : Sym2 V -> Real) (beta h : Real)
    (sigma : V ≃ V)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y)) :
    Measure.map (cfgEquiv (abfsEdgeEquiv sigma)) (abigMeasure J beta h) =
      abigMeasure J beta h := by
  unfold abigMeasure
  exact inhom_map_cfgEquiv (abigParam J beta h)
    (abigParam_le_one J beta h) (abfsEdgeEquiv sigma)
    (abigParam_invariant J beta h sigma hJ)



noncomputable def abigMag (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V)
    (beta h : Real) : Real :=
  (abigMeasure J beta h).real
    (connEvent (withGhost G) Set.univ (some o) {none})

theorem abigMag_nonneg (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V)
    (beta h : Real) : 0 <= abigMag G J o beta h :=
  measureReal_nonneg



theorem abigParam_eq_zero_beta_of_nonpos (J : Sym2 V -> Real) (beta h : Real)
    (hbeta : beta <= 0) (hJ : forall e, 0 <= J e) :
    abigParam J beta h = abigParam J 0 h := by
  funext e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · rfl
      · rfl
      · rfl
      · have hp : pBeta (J s(x, y)) beta <= 0 := by
          unfold pBeta
          have hexp : 1 <= Real.exp (-beta * J s(x, y)) := by
            rw [Real.one_le_exp_iff]
            exact mul_nonneg (neg_nonneg.mpr hbeta) (hJ s(x, y))
          linarith
        simp [abigParam_some_some, Real.toNNReal_eq_zero.mpr hp, pBeta]
        exact mul_nonpos_of_nonpos_of_nonneg hbeta (hJ s(x, y))

theorem abigMag_eq_zero_beta_of_nonpos (G : SimpleGraph V)
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : beta <= 0) (hJ : forall e, 0 <= J e) :
    abigMag G J o beta h = abigMag G J o 0 h := by
  have hm : abigMeasure J beta h = abigMeasure J 0 h := by
    unfold abigMeasure
    congr 1
    exact abigParam_eq_zero_beta_of_nonpos J beta h hbeta hJ
  unfold abigMag
  rw [hm]


theorem abigMag_eq_max_beta_zero (G : SimpleGraph V)
    (J : Sym2 V -> Real) (o : V) (beta h : Real) (hJ : forall e, 0 <= J e) :
    abigMag G J o beta h = abigMag G J o (max beta 0) h := by
  by_cases hbeta : 0 <= beta
  · rw [max_eq_left hbeta]
  · rw [max_eq_right (le_of_not_ge hbeta)]
    exact abigMag_eq_zero_beta_of_nonpos G J o beta h (le_of_not_ge hbeta) hJ



variable {W : Type*}


noncomputable def abigInternalEdges [DecidableEq W] (T : Finset W) :
    Finset (Sym2 W) :=
  (T ×ˢ T).image (fun p => s(p.1, p.2))

theorem mem_abigInternalEdges [DecidableEq W] {T : Finset W} {e : Sym2 W} :
    e ∈ abigInternalEdges T ↔
      ∃ x ∈ T, ∃ y ∈ T, e = s(x, y) := by
  simp only [abigInternalEdges, Finset.mem_image, Finset.mem_product]
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hx, hy⟩, he⟩
    exact ⟨x, hx, y, hy, he.symm⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨(x, y), ⟨hx, hy⟩, rfl⟩



noncomputable def abigInternalEdgeEquiv [DecidableEq W] (T : Finset W) :
    Sym2 T ≃ abigInternalEdges T :=
  Equiv.ofBijective
    (fun e => ⟨Sym2.map (Subtype.val : T -> W) e, by
      induction e using Sym2.inductionOn with
      | _ x y =>
          rw [Sym2.map_mk]
          exact (mem_abigInternalEdges).2
            ⟨x, x.property, y, y.property, rfl⟩⟩)
    ⟨by
      intro e f hef
      apply Sym2.map.injective Subtype.val_injective
      exact congrArg Subtype.val hef,
    by
      rintro ⟨e, he⟩
      obtain ⟨x, hx, y, hy, rfl⟩ := (mem_abigInternalEdges).1 he
      refine ⟨s((⟨x, hx⟩ : T), (⟨y, hy⟩ : T)), ?_⟩
      apply Subtype.ext
      change Sym2.map (Subtype.val : T -> W)
        s((⟨x, hx⟩ : T), (⟨y, hy⟩ : T)) = s(x, y)
      rw [Sym2.map_mk]⟩

@[simp] theorem abigInternalEdgeEquiv_mk [DecidableEq W] (T : Finset W)
    (x y : T) :
    (abigInternalEdgeEquiv T s(x, y) : Sym2 W) = s((x : W), (y : W)) := by
  rw [abigInternalEdgeEquiv]
  simp [Sym2.map_mk]



noncomputable def abigGhostWindow [DecidableEq V] (S : Finset V) :
    Finset (Option V) :=
  S.image some ∪ {none}


noncomputable def abigGhostWindowEquiv [DecidableEq V] (S : Finset V) :
    Option S ≃ abigGhostWindow S :=
  Equiv.ofBijective
    (fun z => match z with
      | none => ⟨none, by simp [abigGhostWindow]⟩
      | some x => ⟨some (x : V), by simp [abigGhostWindow, x.property]⟩)
    ⟨by
      intro a b hab
      rcases a with _ | a <;> rcases b with _ | b <;> simp_all,
    by
      rintro ⟨z, hz⟩
      rcases z with _ | x
      · exact ⟨none, rfl⟩
      · have hx : x ∈ S := by simpa [abigGhostWindow] using hz
        exact ⟨some ⟨x, hx⟩, rfl⟩⟩

@[simp] theorem abigGhostWindowEquiv_none [DecidableEq V] (S : Finset V) :
    (abigGhostWindowEquiv S none : Option V) = none := rfl

@[simp] theorem abigGhostWindowEquiv_some [DecidableEq V] (S : Finset V)
    (x : S) :
    (abigGhostWindowEquiv S (some x) : Option V) = some (x : V) := rfl



noncomputable def abigWindowEdgeEquiv [DecidableEq V] (S : Finset V) :
    Sym2 (Option S) ≃ abigInternalEdges (abigGhostWindow S) :=
  (StatMech.Lattice.sym2Congr (abigGhostWindowEquiv S)).trans
    (abigInternalEdgeEquiv (abigGhostWindow S))

@[simp] theorem abigWindowEdgeEquiv_mk [DecidableEq V] (S : Finset V)
    (a b : Option S) :
    (abigWindowEdgeEquiv S s(a, b) : Sym2 (Option V)) =
      s((abigGhostWindowEquiv S a : Option V),
        (abigGhostWindowEquiv S b : Option V)) := by
  simp [abigWindowEdgeEquiv, StatMech.Lattice.sym2Congr_mk]


def abigWindowGraph (G : SimpleGraph V) (S : Finset V) : SimpleGraph S :=
  G.induce (S : Set V)

instance abigWindowGraph_decidableAdj [DecidableRel G.Adj]
    (S : Finset V) : DecidableRel (abigWindowGraph G S).Adj := by
  intro x y
  change Decidable (G.Adj x y)
  exact inferInstance


noncomputable def abigWindowCoupling (J : Sym2 V -> Real) (S : Finset V) :
    Sym2 S -> Real :=
  fun e => J (Sym2.map (Subtype.val : S -> V) e)

@[simp] theorem abigWindowCoupling_mk (J : Sym2 V -> Real) (S : Finset V)
    (x y : S) :
    abigWindowCoupling J S s(x, y) = J s((x : V), (y : V)) := by
  simp [abigWindowCoupling, Sym2.map_mk]



def abigDartFiberEquivNeighbor {W : Type*} (H : SimpleGraph W) (x : W) :
    {d : H.Dart // d.fst = x} ≃ H.neighborSet x where
  toFun d := ⟨d.1.snd, by simpa only [d.2] using d.1.adj⟩
  invFun y := ⟨H.dartOfNeighborSet x y, rfl⟩
  left_inv d := by
    rcases d with ⟨⟨⟨a, b⟩, hab⟩, ha⟩
    simp only at ha
    subst a
    rfl
  right_inv y := by
    apply Subtype.ext
    rfl




theorem abigWindow_incidentCoupling_eq_sum [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (x : S) :
    abcrIncidentCoupling (abigWindowGraph G S)
        (abigWindowCoupling J S) x =
      ∑ y : S, if G.Adj (x : V) (y : V)
        then J s((x : V), (y : V)) else 0 := by
  unfold abcrIncidentCoupling
  calc
    (∑ d : {d : (abigWindowGraph G S).Dart // d.fst = x},
        abigWindowCoupling J S d.1.edge) =
        ∑ y : (abigWindowGraph G S).neighborSet x,
          J s((x : V), (y.1 : V)) := by
      apply Fintype.sum_equiv
        (abigDartFiberEquivNeighbor (abigWindowGraph G S) x)
      intro d
      simp [abigDartFiberEquivNeighbor, abigWindowCoupling,
        SimpleGraph.Dart.edge, d.2]
    _ = ∑ y : S, if G.Adj (x : V) (y : V)
          then J s((x : V), (y : V)) else 0 := by
      rw [← Finset.sum_subtype
        (Finset.univ.filter fun y : S => (abigWindowGraph G S).Adj x y)
        (by intro y; simp) (fun y : S => J s((x : V), (y : V)))]
      rw [Finset.sum_filter]
      rfl




def abigUniformFiniteRowBound (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (J0 : Real) : Prop :=
  forall (S : Finset V) (x : S),
    (∑ y : S, if G.Adj (x : V) (y : V)
      then J s((x : V), (y : V)) else 0) <= J0



theorem abigWindow_incidentCoupling_le [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (J0 : Real)
    (hrow : abigUniformFiniteRowBound G J J0)
    (S : Finset V) (x : S) :
    abcrIncidentCoupling (abigWindowGraph G S)
      (abigWindowCoupling J S) x <= J0 := by
  rw [abigWindow_incidentCoupling_eq_sum G J S x]
  exact hrow S x



theorem abigUniformFiniteRowBound_of_tsum [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (J0 : Real)
    (hJ : forall e, 0 <= J e)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0) :
    abigUniformFiniteRowBound G J J0 := by
  intro S x
  change (∑ y : S, (fun z : V =>
    if G.Adj (x : V) z then J s((x : V), z) else 0) y) <= J0
  calc
    _ = ∑ y ∈ S, if G.Adj (x : V) y
        then J s((x : V), y) else 0 := Finset.sum_coe_sort S _
    _ <= ∑' y, if G.Adj (x : V) y
        then J s((x : V), y) else 0 :=
      Summable.sum_le_tsum S (by
        intro y hy
        by_cases hxy : G.Adj (x : V) y
        · simp [hxy, hJ]
        · simp [hxy]) (hsum (x : V))
    _ <= J0 := hrow (x : V)



theorem abigWindow_abfaParams_eq [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (beta h : Real)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0) :
    forall e : Sym2 (Option S),
      abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h e =
        abigRealParam J beta h (abigWindowEdgeEquiv S e) := by
  intro e
  induction e using Sym2.inductionOn with
  | _ a b =>
      rcases a with _ | x <;> rcases b with _ | y
      · simp [abfaParams, abpdBetaFieldParams, paramOn, abfaLiftCoupling,
          abfaBaseCoupling, abigRealParam, FieldGhostDict.ghostCoupling,
          FieldGhostDict.ghostEdges, abigWindowEdgeEquiv, pBeta]
      · simp [abfaParams, abpdBetaFieldParams, paramOn, abigRealParam,
          FieldGhostDict.ghostCoupling, FieldGhostDict.ghostEdges,
          abigWindowEdgeEquiv]
      · simp [abfaParams, abpdBetaFieldParams, paramOn, abigRealParam,
          FieldGhostDict.ghostCoupling, FieldGhostDict.ghostEdges,
          abigWindowEdgeEquiv]
      · simp only [abfaParams, abpdBetaFieldParams, paramOn,
          abigWindowEdgeEquiv_mk, abigGhostWindowEquiv_some,
          abigRealParam_some_some]
        have hnotGhost : s(some x, some y) ∉
            FieldGhostDict.ghostEdges S := by
          simp [FieldGhostDict.ghostEdges]
        rw [if_neg hnotGhost, abfaLiftCoupling_some_some,
          abigWindowCoupling_mk]
        by_cases hxy : G.Adj x y
        · have hind : s(x, y) ∈ (abigWindowGraph G S).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset]
            exact hxy
          rw [if_pos hind]
        · have hind : s(x, y) ∉ (abigWindowGraph G S).edgeFinset := by
            rw [SimpleGraph.mem_edgeFinset]
            exact hxy
          rw [if_neg hind, hJsupport x y hxy]



theorem abigWindow_openSub_adj [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (eta : ConfigSpace (abigInternalEdges (abigGhostWindow S)))
    (a b : Option S) :
    (openSub (withGhost (abigWindowGraph G S))
        (cfgEquiv (abigWindowEdgeEquiv S) eta)).Adj a b ↔
      (openSub (withGhost G)
        (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).Adj
        (abigGhostWindowEquiv S a : Option V)
        (abigGhostWindowEquiv S b : Option V) := by
  have hcoord : forall c d : Option S,
      cfgEquiv (abigWindowEdgeEquiv S) eta s(c, d) =
        ih_fill (abigInternalEdges (abigGhostWindow S)) eta
          s((abigGhostWindowEquiv S c : Option V),
            (abigGhostWindowEquiv S d : Option V)) := by
    intro c d
    have he : s((abigGhostWindowEquiv S c : Option V),
        (abigGhostWindowEquiv S d : Option V)) ∈
          abigInternalEdges (abigGhostWindow S) :=
      (mem_abigInternalEdges).2
        ⟨abigGhostWindowEquiv S c, (abigGhostWindowEquiv S c).property,
          abigGhostWindowEquiv S d, (abigGhostWindowEquiv S d).property, rfl⟩
    rw [cfgEquiv_apply, ih_fill, dif_pos he]
    congr 1
  rcases a with _ | x <;> rcases b with _ | y <;>
    simp [openSub, withGhost, abigWindowGraph, hcoord]



theorem abigWindow_connWithin [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (eta : ConfigSpace (abigInternalEdges (abigGhostWindow S)))
    (a b : Option S) :
    ConnWithin (withGhost (abigWindowGraph G S))
        (cfgEquiv (abigWindowEdgeEquiv S) eta) Set.univ
        ⟨a, Set.mem_univ _⟩ ⟨b, Set.mem_univ _⟩ ↔
      ConnWithin (withGhost G)
        (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)
        (abigGhostWindow S : Set (Option V))
        ⟨abigGhostWindowEquiv S a, (abigGhostWindowEquiv S a).property⟩
        ⟨abigGhostWindowEquiv S b, (abigGhostWindowEquiv S b).property⟩ := by
  constructor
  · intro hconn
    let f :
        ((openSub (withGhost (abigWindowGraph G S))
          (cfgEquiv (abigWindowEdgeEquiv S) eta)).induce Set.univ) →g
        ((openSub (withGhost G)
          (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).induce
            (abigGhostWindow S : Set (Option V))) :=
      { toFun := fun z =>
          ⟨abigGhostWindowEquiv S z, (abigGhostWindowEquiv S z).property⟩
        map_rel' := fun {x y} hxy =>
          (abigWindow_openSub_adj G S eta x y).mp hxy }
    exact hconn.map f
  · intro hconn
    let f :
        ((openSub (withGhost G)
          (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)).induce
            (abigGhostWindow S : Set (Option V))) →g
        ((openSub (withGhost (abigWindowGraph G S))
          (cfgEquiv (abigWindowEdgeEquiv S) eta)).induce Set.univ) :=
      { toFun := fun z => ⟨(abigGhostWindowEquiv S).symm z, Set.mem_univ _⟩
        map_rel' := fun {x y} hxy => by
          apply (abigWindow_openSub_adj G S eta
            ((abigGhostWindowEquiv S).symm x)
            ((abigGhostWindowEquiv S).symm y)).mpr
          simpa using hxy }
    convert hconn.map f using 1 <;> simp [f]



theorem abigWindow_preimage_connEvent [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (o : S) :
    (cfgEquiv (abigWindowEdgeEquiv S)) ⁻¹'
        connEvent (withGhost (abigWindowGraph G S)) Set.univ
          (some o) {none} =
      ih_section
        (connEvent (withGhost G) (abigGhostWindow S : Set (Option V))
          (some (o : V)) {none})
        (abigInternalEdges (abigGhostWindow S)) := by
  ext eta
  change ConnToSet (withGhost (abigWindowGraph G S))
      (cfgEquiv (abigWindowEdgeEquiv S) eta) Set.univ (some o) {none} ↔
    ConnToSet (withGhost G)
      (ih_fill (abigInternalEdges (abigGhostWindow S)) eta)
      (abigGhostWindow S : Set (Option V)) (some (o : V)) {none}
  constructor
  · rintro ⟨_, b, _, hb, hconn⟩
    have hbnone : b = none := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨(abigGhostWindowEquiv S (some o)).property, none,
      (abigGhostWindowEquiv S none).property, rfl,
      (abigWindow_connWithin G S eta (some o) none).mp hconn⟩
  · rintro ⟨_, b, _, hb, hconn⟩
    have hbnone : b = none := Set.mem_singleton_iff.mp hb
    subst b
    exact ⟨Set.mem_univ _, none, Set.mem_univ _, rfl,
      (abigWindow_connWithin G S eta (some o) none).mpr hconn⟩



theorem abig_connEvent_congr [DecidableEq W] (G : SimpleGraph W)
    (T : Finset W) (u v : W) {omega omega' : ConfigSpace (Sym2 W)}
    (hagree : ∀ e ∈ abigInternalEdges T, omega e = omega' e) :
    omega ∈ connEvent G (T : Set W) u {v} ↔
      omega' ∈ connEvent G (T : Set W) u {v} := by
  have hforward : ∀ {eta eta' : ConfigSpace (Sym2 W)},
      (∀ e ∈ abigInternalEdges T, eta e = eta' e) →
      eta ∈ connEvent G (T : Set W) u {v} →
      eta' ∈ connEvent G (T : Set W) u {v} := by
    intro eta eta' heq hconn
    rcases hconn with ⟨hu, b, hb, hbv, ⟨walk⟩⟩
    have hb_eq : b = v := Set.mem_singleton_iff.mp hbv
    subst b
    refine ⟨hu, v, hb, rfl, ⟨sab_inducedWalkTransfer G walk ?_⟩⟩
    intro e he
    apply heq e
    rcases he with ⟨z, hz, rfl⟩
    induction z using Sym2.inductionOn with
    | _ x y =>
        rw [Sym2.map_mk]
        exact (mem_abigInternalEdges).2
          ⟨x, x.property, y, y.property, rfl⟩
  constructor
  · exact hforward hagree
  · exact hforward (fun e he => (hagree e he).symm)


theorem abig_connEvent_dependsOn [DecidableEq W] (G : SimpleGraph W)
    (T : Finset W) (u v : W) :
    StatMech.DependsOn (connEvent G (T : Set W) u {v})
      (abigInternalEdges T : Set (Sym2 W)) := by
  intro omega omega' hagree
  exact abig_connEvent_congr G T u v
    (fun e he => (hagree e (by simpa using he)).symm)


theorem abig_measurableSet_connEvent [Countable W] [DecidableEq W]
    (G : SimpleGraph W) (T : Finset W) (u v : W) :
    MeasurableSet (connEvent G (T : Set W) u {v}) := by
  rw [ih_eq_cylinder_of_dependsOn (abigInternalEdges T)
    (abig_connEvent_dependsOn G T u v)]
  exact MeasurableSet.cylinder _ MeasurableSet.of_discrete


theorem abig_connWithin_mono_set (G : SimpleGraph W)
    (omega : ConfigSpace (Sym2 W)) {S T : Set W} (hST : S ⊆ T)
    {x y : S} (hconn : ConnWithin G omega S x y) :
    ConnWithin G omega T ⟨x, hST x.property⟩ ⟨y, hST y.property⟩ := by
  let f : ((openSub G omega).induce S) →g ((openSub G omega).induce T) :=
    { toFun := fun z => ⟨z, hST z.property⟩
      map_rel' := fun hab => hab }
  exact hconn.map f


theorem abig_connEvent_mono_set (G : SimpleGraph W) {S T : Set W}
    (hST : S ⊆ T) (u v : W) :
    connEvent G S u {v} ⊆ connEvent G T u {v} := by
  rintro omega ⟨hu, b, hb, hbv, hconn⟩
  refine ⟨hST hu, b, hST hb, hbv, ?_⟩
  exact abig_connWithin_mono_set G omega hST hconn




theorem abig_iUnion_connEvent_exhaustion [DecidableEq W]
    (G : SimpleGraph W) (T : Nat -> Finset W) (u v : W)
    (hcover : forall F : Finset W, exists n, F ⊆ T n) :
    (⋃ n, connEvent G (T n : Set W) u {v}) =
      connEvent G Set.univ u {v} := by
  ext omega
  constructor
  · rintro homega
    rw [Set.mem_iUnion] at homega
    obtain ⟨n, hn⟩ := homega
    exact abig_connEvent_mono_set G (Set.subset_univ _) u v hn
  · intro homega
    rcases homega with ⟨hu, b, hb, hbv, ⟨walk⟩⟩
    have hb_eq : b = v := Set.mem_singleton_iff.mp hbv
    subst b
    let ambient : (openSub G omega).Walk u v :=
      walk.map (SimpleGraph.Embedding.induce Set.univ).toHom
    obtain ⟨n, hn⟩ := hcover ambient.support.toFinset
    have hsupp : ∀ z, z ∈ ambient.support → z ∈ (T n : Set W) := by
      intro z hz
      exact hn (List.mem_toFinset.mpr hz)
    have huT : u ∈ (T n : Set W) := hsupp u ambient.start_mem_support
    have hvT : v ∈ (T n : Set W) := hsupp v ambient.end_mem_support
    rw [Set.mem_iUnion]
    refine ⟨n, huT, v, hvT, rfl, ?_⟩
    exact ⟨ambient.induce (T n : Set W) hsupp⟩



theorem abig_measurableSet_connEvent_univ [Countable W] [DecidableEq W]
    (G : SimpleGraph W) (T : Nat -> Finset W) (u v : W)
    (hcover : forall F : Finset W, exists n, F ⊆ T n) :
    MeasurableSet (connEvent G Set.univ u {v}) := by
  rw [← abig_iUnion_connEvent_exhaustion G T u v hcover]
  exact MeasurableSet.iUnion (fun n => abig_measurableSet_connEvent G (T n) u v)



theorem abig_tendsto_real_connEvent_exhaustion
    [Countable W] [DecidableEq W]
    (mu : Measure (ConfigSpace (Sym2 W))) [IsFiniteMeasure mu]
    (G : SimpleGraph W) (T : Nat -> Finset W) (u v : W)
    (hmono : Monotone T)
    (hcover : forall F : Finset W, exists n, F ⊆ T n) :
    Tendsto
      (fun n => mu.real (connEvent G (T n : Set W) u {v}))
      atTop (nhds (mu.real (connEvent G Set.univ u {v}))) := by
  let A : Nat -> Set (ConfigSpace (Sym2 W)) :=
    fun n => connEvent G (T n : Set W) u {v}
  have hAmono : Monotone A := by
    intro n m hnm
    exact abig_connEvent_mono_set G
      (fun x hx => hmono hnm hx) u v
  have hlim := tendsto_measure_iUnion_atTop (μ := mu) hAmono
  rw [abig_iUnion_connEvent_exhaustion G T u v hcover] at hlim
  exact (ENNReal.tendsto_toReal (measure_ne_top mu _)).comp hlim

section Marginals

variable [Countable V]




theorem abigMag_eq_of_automorphism [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (sigma : V ≃ V)
    (hG : forall x y, G.Adj (sigma x) (sigma y) <-> G.Adj x y)
    (hJ : forall x y, J s(sigma x, sigma y) = J s(x, y))
    (T : Nat -> Finset (Option V))
    (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
    abigMag G J (sigma o) beta h = abigMag G J o beta h := by
  let A := connEvent (withGhost G) Set.univ (some o) {none}
  have hA : MeasurableSet A := by
    exact abig_measurableSet_connEvent_univ
      (withGhost G) T (some o) none hcover
  have hpush := congrArg (fun mu :
      Measure (ConfigSpace (Sym2 (Option V))) => mu A)
    (abig_map_cfgEquiv J beta h sigma hJ)
  change (Measure.map (cfgEquiv (abfsEdgeEquiv sigma))
      (abigMeasure J beta h)) A = (abigMeasure J beta h) A at hpush
  rw [Measure.map_apply (measurable_cfgEquiv (abfsEdgeEquiv sigma)) hA,
    abfs_preimage_connEvent G sigma hG o] at hpush
  unfold abigMag Measure.real
  exact congrArg ENNReal.toReal hpush



theorem abigMag_eq_of_transitive [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJ : forall x u v, J s(move x u, move x v) = J s(u, v))
    (T : Nat -> Finset (Option V))
    (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
    forall x, abigMag G J x beta h = abigMag G J o beta h := by
  intro x
  rw [← hmove x]
  exact abigMag_eq_of_automorphism G J o beta h (move x)
    (hG x) (hJ x) T hcover


theorem abig_coord_true_prob (J : Sym2 V -> Real) (beta h : Real)
    (e : Sym2 (Option V)) :
    (abigMeasure J beta h).real {omega | omega e = true} =
      (abigParam J beta h e : Real) := by
  classical
  exact inhom_coord_true_prob (abigParam J beta h)
    (abigParam_le_one J beta h) e



theorem abig_realProb_cylinder (J : Sym2 V -> Real) (beta h : Real)
    (F : Finset (Sym2 (Option V)))
    (A : Set (ConfigSpace F)) :
    (abigMeasure J beta h).real (MeasureTheory.cylinder F A) =
      (inhomBernoulliProductMeasure
        (fun e : F => abigParam J beta h e)
        (fun e => abigParam_le_one J beta h e)).real A := by
  classical
  exact inhom_realProb_cylinder (abigParam J beta h)
    (abigParam_le_one J beta h) F A



theorem abig_finite_conn_prob_eq_marginal [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (T : Finset (Option V)) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) =
      (inhomBernoulliProductMeasure
        (fun e : abigInternalEdges T => abigParam J beta h e)
        (fun e => abigParam_le_one J beta h e)).real
        (ih_section
          (connEvent (withGhost G) (T : Set (Option V)) (some o) {none})
          (abigInternalEdges T)) := by
  classical
  let A := connEvent (withGhost G) (T : Set (Option V)) (some o) {none}
  let F := abigInternalEdges T
  have hAcyl : A = MeasureTheory.cylinder F (ih_section A F) :=
    ih_eq_cylinder_of_dependsOn F
      (abig_connEvent_dependsOn (withGhost G) T (some o) none)
  calc
    (abigMeasure J beta h).real A =
        (abigMeasure J beta h).real
          (MeasureTheory.cylinder F (ih_section A F)) := congrArg _ hAcyl
    _ = (inhomBernoulliProductMeasure
          (fun e : F => abigParam J beta h e)
          (fun e => abigParam_le_one J beta h e)).real
          (ih_section A F) := abig_realProb_cylinder J beta h F _



theorem abig_finite_conn_prob_eq_probV [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (T : Finset (Option V)) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) =
      probV (fun e : abigInternalEdges T => abigRealParam J beta h e)
        (ih_section
          (connEvent (withGhost G) (T : Set (Option V)) (some o) {none})
          (abigInternalEdges T)) := by
  rw [abig_finite_conn_prob_eq_marginal G J o beta h T]
  let r : abigInternalEdges T -> Real :=
    fun e => abigRealParam J beta h e
  have hr := fun e => abigRealParam_mem J beta h hbeta hh hJ e
  simpa [r, abigParam] using
    (inhom_real_eq_probV_of_mem r (fun e => (hr e).1)
      (fun e => (hr e).2)
      (ih_section
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none})
        (abigInternalEdges T)))



theorem abig_abfaMag_eq_finiteConn [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0) :
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta h =
      (abigMeasure J beta h).real
        (connEvent (withGhost G)
          (abigGhostWindow S : Set (Option V)) (some (o : V)) {none}) := by
  unfold abfaMag
  rw [abfs_probV_transfer (abigWindowEdgeEquiv S)]
  have hp : (fun y =>
      abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h
        ((abigWindowEdgeEquiv S).symm y)) =
      fun y : abigInternalEdges (abigGhostWindow S) =>
        abigRealParam J beta h y := by
    funext y
    simpa using abigWindow_abfaParams_eq G J S beta h hJsupport
      ((abigWindowEdgeEquiv S).symm y)
  rw [hp, abigWindow_preimage_connEvent G S o]
  exact (abig_finite_conn_prob_eq_probV G J (o : V) beta h
    hbeta hh hJ (abigGhostWindow S)).symm


noncomputable def abigWindowEnvelope [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h : Real) : Real :=
  (Finset.univ.image (fun x : S =>
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h)).max'
      (by exact Finset.image_nonempty.mpr ⟨o, Finset.mem_univ o⟩)

omit [Countable V] in

theorem abigWindowMag_le_envelope [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o x : S) (beta h : Real) :
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <=
      abigWindowEnvelope G J S o beta h := by
  apply Finset.le_max'
  exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩



theorem abigWindowEnvelope_monotoneOn_beta [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (h : Real)
    (hJ : forall e, 0 <= J e) (hh : 0 <= h) :
    MonotoneOn (fun beta => abigWindowEnvelope G J S o beta h) (Ici 0) := by
  intro beta hbeta gamma hgamma hbg
  unfold abigWindowEnvelope
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  calc
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <=
        abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x gamma h := by
      apply abfaMag_monotoneOn_beta
        (abigWindowGraph G S) (abigWindowCoupling J S) x h
      · intro e he
        induction e using Sym2.inductionOn with
        | _ a b => simpa using hJ s((a : V), (b : V))
      · exact hh
      · exact hbeta
      · exact hgamma
      · exact hbg
    _ <= _ := abigWindowMag_le_envelope G J S o x gamma h



theorem abigWindowEnvelope_monotoneOn_field [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta : Real)
    (hJ : forall e, 0 <= J e) (hbeta : 0 <= beta) :
    MonotoneOn (fun h => abigWindowEnvelope G J S o beta h) (Ici 0) := by
  intro h hh t ht hht
  unfold abigWindowEnvelope
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  calc
    abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta h <=
        abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) x beta t := by
      apply abfaMag_monotoneOn_field
        (abigWindowGraph G S) (abigWindowCoupling J S) x beta
      · intro e he
        induction e using Sym2.inductionOn with
        | _ a b => simpa using hJ s((a : V), (b : V))
      · exact hbeta
      · exact hh
      · exact ht
      · exact hht
    _ <= _ := abigWindowMag_le_envelope G J S o x beta t



theorem abig_window_aizenmanBarsky_finiteEnvelope [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h J0 : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hrow : forall x : S,
      abcrIncidentCoupling (abigWindowGraph G S)
        (abigWindowCoupling J S) x <= J0) :
    deriv (fun b =>
      abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o b h) beta <=
      J0 * abigWindowEnvelope G J S o beta h *
        deriv (fun t =>
          abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta t) h := by
  have hJwin : ∀ e, e ∈ (abigWindowGraph G S).edgeFinset →
      0 <= abigWindowCoupling J S e := by
    intro e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hp := abfaParams_mem (abigWindowGraph G S)
    (abigWindowCoupling J S) hJwin beta h hbeta hh
  have hU : 0 <= abigWindowEnvelope G J S o beta h := by
    exact (abgi_probV_nonneg
      (abfaParams (abigWindowGraph G S) (abigWindowCoupling J S) beta h)
      hp _).trans (abigWindowMag_le_envelope G J S o o beta h)
  apply abfa_aizenmanBarsky_le_envelope
    (abigWindowGraph G S) (abigWindowCoupling J S) o beta h J0
    (abigWindowEnvelope G J S o beta h)
  · exact hJwin
  · exact hrow
  · exact hbeta
  · exact hh
  · exact hU
  · intro x
    exact abigWindowMag_le_envelope G J S o x beta h



theorem abigWindowEnvelope_le_mag [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hInfiniteTarget : forall x : S,
      abigMag G J (x : V) beta h <= abigMag G J (o : V) beta h) :
    abigWindowEnvelope G J S o beta h <= abigMag G J (o : V) beta h := by
  unfold abigWindowEnvelope
  rw [Finset.max'_le_iff]
  intro z hz
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  rw [abig_abfaMag_eq_finiteConn G J S x beta h
    hbeta hh hJ hJsupport]
  apply le_trans ?_ (hInfiniteTarget x)
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact abig_connEvent_mono_set (withGhost G) (Set.subset_univ _)
    (some (x : V)) none




theorem abig_window_aizenmanBarsky [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (S : Finset V) (o : S) (beta h J0 : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hrow : forall x : S,
      abcrIncidentCoupling (abigWindowGraph G S)
        (abigWindowCoupling J S) x <= J0)
    (hInfiniteTarget : forall x : S,
      abigMag G J (x : V) beta h <= abigMag G J (o : V) beta h) :
    deriv (fun b =>
      abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o b h) beta <=
      J0 * abigMag G J (o : V) beta h *
        deriv (fun t =>
          abfaMag (abigWindowGraph G S) (abigWindowCoupling J S) o beta t) h := by
  apply abfa_aizenmanBarsky_le_envelope
    (abigWindowGraph G S) (abigWindowCoupling J S) o beta h J0
    (abigMag G J (o : V) beta h)
  · intro e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  · exact hrow
  · exact hbeta
  · exact hh
  · exact abigMag_nonneg G J (o : V) beta h
  · intro x
    change abfaMag (abigWindowGraph G S) (abigWindowCoupling J S)
      x beta h <= abigMag G J (o : V) beta h
    rw [abig_abfaMag_eq_finiteConn G J S x beta h
      hbeta hh hJ hJsupport]
    apply le_trans ?_ (hInfiniteTarget x)
    apply measureReal_mono (h₂ := measure_ne_top _ _)
    exact abig_connEvent_mono_set (withGhost G) (Set.subset_univ _)
      (some (x : V)) none



theorem abig_tendsto_mag_exhaustion [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (T : Nat -> Finset (Option V)) (hmono : Monotone T)
    (hcover : forall F : Finset (Option V), exists n, F ⊆ T n) :
    Tendsto
      (fun n => (abigMeasure J beta h).real
        (connEvent (withGhost G) (T n : Set (Option V)) (some o) {none}))
      atTop (nhds (abigMag G J o beta h)) := by
  simpa [abigMag] using
    (abig_tendsto_real_connEvent_exhaustion (abigMeasure J beta h)
      (withGhost G) T (some o) none hmono hcover)



theorem abig_tendsto_abfaMag_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 <= h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmono : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    Tendsto
      (fun n => abfaMag (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) ⟨o, ho n⟩ beta h)
      atTop (nhds (abigMag G J o beta h)) := by
  apply Filter.Tendsto.congr'
    (Filter.Eventually.of_forall (fun n =>
      (abig_abfaMag_eq_finiteConn G J (S n) ⟨o, ho n⟩ beta h
        hbeta hh hJ hJsupport).symm))
  exact abig_tendsto_mag_exhaustion G J o beta h
    (fun n => abigGhostWindow (S n)) hmono hcover



theorem abigMag_monotoneOn_field_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta : Real) (hbeta : 0 <= beta)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    MonotoneOn (fun h => abigMag G J o beta h) (Ici 0) := by
  intro h1 hh1 h2 hh2 h12
  apply le_of_tendsto_of_tendsto
    (abig_tendsto_abfaMag_exhaustion G J o beta h1 hbeta hh1 hJ hJsupport
      S ho hmonoWindow hcover)
    (abig_tendsto_abfaMag_exhaustion G J o beta h2 hbeta hh2 hJ hJsupport
      S ho hmonoWindow hcover)
  exact Filter.Eventually.of_forall (fun n => by
    apply abfaMag_monotoneOn_field
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ beta
    · intro e he
      induction e using Sym2.inductionOn with
      | _ x y => simpa using hJ s((x : V), (y : V))
    · exact hbeta
    · exact hh1
    · exact hh2
    · exact h12)




theorem abigMag_continuousAt_field_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 < h)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    ContinuousAt (fun t => abigMag G J o beta t) h := by
  let Mn : Nat -> Real -> Real := fun n t =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ beta t
  have hJwin : forall (n : Nat) (e : Sym2 (S n)),
      e ∈ (abigWindowGraph G (S n)).edgeFinset ->
        0 <= abigWindowCoupling J (S n) e := by
    intro n e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hlocal : forall t, |t - h| < h / 2 ->
      |abigMag G J o beta t - abigMag G J o beta h| <=
        (2 / h) * |t - h| := by
    intro t ht
    have htpos : 0 < t := by
      have hlower : h - t <= |t - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - t)
      linarith
    have hfinite : forall n,
        |Mn n t - Mn n h| <= (2 / h) * |t - h| := by
      intro n
      have hderiv : forall (u : Real), u ∈ Set.uIcc h t ->
          ‖deriv (Mn n) u‖ <= 2 / h := by
        intro u hu
        have hudist : |u - h| <= |t - h| := abs_sub_left_of_mem_uIcc hu
        have hupos : 0 < u := by
          have hlower : h - u <= |u - h| := by
            rw [abs_sub_comm]
            exact le_abs_self (h - u)
          linarith
        have hnonneg : 0 <= deriv (Mn n) u := by
          apply abfa_deriv_field_nonneg
            (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              ⟨o, ho n⟩ beta u (hJwin n) hbeta hupos.le
        have hupper : deriv (Mn n) u <= 1 / u := by
          exact abgr_deriv_abfaMag_field_le
            (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              (hJwin n) ⟨o, ho n⟩ beta u hbeta hupos
        rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
        exact hupper.trans ((div_le_div_iff₀ hupos hh).mpr (by
          have : h <= 2 * u := by
            have hlower : h - u <= |u - h| := by
              rw [abs_sub_comm]
              exact le_abs_self (h - u)
            linarith
          simpa using this))
      have hmvt := (convex_uIcc h t).norm_image_sub_le_of_norm_deriv_le
        (f := Mn n) (C := 2 / h)
        (fun u _ => (abgr_hasDerivAt_abfaMag_field
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ beta u).differentiableAt)
        hderiv left_mem_uIcc right_mem_uIcc
      simpa [Real.norm_eq_abs] using hmvt
    have htend : Tendsto (fun n => |Mn n t - Mn n h|) atTop
        (nhds |abigMag G J o beta t - abigMag G J o beta h|) :=
      ((abig_tendsto_abfaMag_exhaustion G J o beta t hbeta htpos.le hJ hJsupport
          S ho hmonoWindow hcover).sub
        (abig_tendsto_abfaMag_exhaustion G J o beta h hbeta hh.le hJ hJsupport
          S ho hmonoWindow hcover)).abs
    exact le_of_tendsto htend (Filter.Eventually.of_forall hfinite)
  rw [Metric.continuousAt_iff]
  intro epsilon hepsilon
  refine ⟨min (h / 2) (epsilon * h / 2), by positivity, ?_⟩
  intro t hdist
  rw [Real.dist_eq] at hdist ⊢
  have ht : |t - h| < h / 2 :=
    lt_of_lt_of_le hdist (min_le_left _ _)
  calc
    |abigMag G J o beta t - abigMag G J o beta h| <=
        (2 / h) * |t - h| := hlocal t ht
    _ < (2 / h) * (epsilon * h / 2) := by
      apply mul_lt_mul_of_pos_left
      · exact lt_of_lt_of_le hdist (min_le_right _ _)
      · positivity
    _ = epsilon := by field_simp





theorem abigMag_differentiableAt_field_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hbeta : 0 <= beta) (hh : 0 < h)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    DifferentiableAt Real (fun t => abigMag G J o beta t) h := by
  let Mn : Nat -> Real -> Real := fun n t =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ beta t
  let dn : Nat -> Real := fun n => deriv (Mn n) h
  have hJwin : forall (n : Nat) (e : Sym2 (S n)),
      e ∈ (abigWindowGraph G (S n)).edgeFinset ->
        0 <= abigWindowCoupling J (S n) e := by
    intro n e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hlim : forall y, |y - h| < h / 2 ->
      Tendsto (fun n => Mn n y) atTop (nhds (abigMag G J o beta y)) := by
    intro y hy
    have hypos : 0 < y := by
      have hlower : h - y <= |y - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - y)
      linarith
    exact abig_tendsto_abfaMag_exhaustion G J o beta y hbeta hypos.le
      hJ hJsupport S ho hmonoWindow hcover
  have htaylor : forall n y, |y - h| < h / 2 ->
      |Mn n y - Mn n h - dn n * (y - h)| <=
        (8 / h ^ 2) * |y - h| ^ 2 := by
    intro n y hy
    have hpos_on : forall (z : Real), z ∈ Set.uIcc h y -> 0 < z := by
      intro z hz
      have hzdist : |z - h| <= |y - h| := abs_sub_left_of_mem_uIcc hz
      have hlower : h - z <= |z - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - z)
      linarith
    apply abgr_taylor_remainder_le (Mn n) h y (8 / h ^ 2) (by positivity)
    · intro z hz
      exact (abgr_hasDerivAt_abfaMag_field
        (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
          ⟨o, ho n⟩ beta z).differentiableAt
    · intro z hz
      exact (abgr_hasDerivAt_deriv_abfaMag_field
        (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
          ⟨o, ho n⟩ beta z).differentiableAt
    · intro z hz
      have hzpos := hpos_on z hz
      have hsecond := abgr_abs_deriv_deriv_abfaMag_field_le
        (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
          (hJwin n) ⟨o, ho n⟩ beta z hbeta hzpos
      exact hsecond.trans ((div_le_div_iff₀ (sq_pos_of_pos hzpos)
        (sq_pos_of_pos hh)).mpr (by
          have hzdist : |z - h| <= |y - h| := abs_sub_left_of_mem_uIcc hz
          have hlower : h - z <= |z - h| := by
            rw [abs_sub_comm]
            exact le_abs_self (h - z)
          have hzhalf : h / 2 < z := by linarith
          nlinarith [sq_nonneg (2 * z - h)]))
  obtain ⟨L, hL⟩ := abgr_hasDerivAt_limit_of_taylor Mn
    (fun t => abigMag G J o beta t) dn h (h / 2) (8 / h ^ 2)
      (by linarith) (by positivity) hlim htaylor
  exact hL.differentiableAt



theorem abigMag_beta_lipschitz_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 beta gamma h : Real)
    (hJ0 : 0 <= J0) (hbeta : 0 <= beta) (hgamma : 0 <= gamma)
    (hh : 0 < h) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall b t, 0 <= b -> 0 <= t ->
      forall n (x : S n),
        abigMag G J (x : V) b t <= abigMag G J o b t)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    |abigMag G J o gamma h - abigMag G J o beta h| <=
      (J0 / h) * |gamma - beta| := by
  let Mn : Nat -> Real -> Real := fun n b =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ b h
  let Cn : Nat -> Real -> Real := fun n b =>
    abigWindowEnvelope G J (S n) ⟨o, ho n⟩ b h
  have hJwin : forall (n : Nat) (e : Sym2 (S n)),
      e ∈ (abigWindowGraph G (S n)).edgeFinset ->
        0 <= abigWindowCoupling J (S n) e := by
    intro n e he
    induction e using Sym2.inductionOn with
    | _ x y => simpa using hJ s((x : V), (y : V))
  have hfinite : forall n,
      |Mn n gamma - Mn n beta| <= (J0 / h) * |gamma - beta| := by
    intro n
    have hderiv : forall (b : Real), b ∈ Set.uIcc beta gamma ->
        ‖deriv (Mn n) b‖ <= J0 / h := by
      intro b hb
      have hb0 : 0 <= b := by
        rw [Set.mem_uIcc] at hb
        rcases hb with hb | hb <;> linarith
      have hbetaNN : 0 <= deriv (Mn n) b := by
        apply abfa_deriv_beta_nonneg
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b h (hJwin n) hb0 hh.le
      have hAB := abig_window_aizenmanBarsky_finiteEnvelope
        G J (S n) ⟨o, ho n⟩ b h J0 hb0 hh.le hJ (hrow n)
      change deriv (Mn n) b <=
        J0 * Cn n b * deriv (fun t =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b t) h at hAB
      have hCn1 : Cn n b <= 1 := by
        calc
          Cn n b <= abigMag G J o b h :=
            abigWindowEnvelope_le_mag G J (S n) ⟨o, ho n⟩ b h
              hb0 hh.le hJ hJsupport (hInfiniteTarget b h hb0 hh.le n)
          _ <= 1 := measureReal_le_one
      have hfield0 : 0 <= deriv (fun t =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b t) h :=
        abfa_deriv_field_nonneg
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b h (hJwin n) hb0 hh.le
      have hfield1 : deriv (fun t =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b t) h <= 1 / h :=
        abgr_deriv_abfaMag_field_le
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            (hJwin n) ⟨o, ho n⟩ b h hb0 hh
      rw [Real.norm_eq_abs, abs_of_nonneg hbetaNN]
      calc
        deriv (Mn n) b <= J0 * Cn n b * deriv (fun t =>
            abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              ⟨o, ho n⟩ b t) h := hAB
        _ <= J0 * 1 * deriv (fun t =>
            abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
              ⟨o, ho n⟩ b t) h :=
          by
            simpa [mul_assoc] using
              (mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hCn1 hfield0) hJ0)
        _ <= J0 * (1 / h) := by
          simpa using mul_le_mul_of_nonneg_left hfield1 hJ0
        _ = J0 / h := by ring
    have hmvt := (convex_uIcc beta gamma).norm_image_sub_le_of_norm_deriv_le
      (f := Mn n) (C := J0 / h)
      (fun b _ => by
        change DifferentiableAt Real (fun u =>
          abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ u h) b
        have hjoint := abfa_differentiableAt_mag_joint
          (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
            ⟨o, ho n⟩ b h
        have hpair : DifferentiableAt Real (fun u : Real => (u, h)) b :=
          differentiableAt_id.prodMk (differentiableAt_const h)
        have hc := DifferentiableAt.comp (f := fun u : Real => (u, h))
          (g := Function.uncurry (abfaMag (abigWindowGraph G (S n))
            (abigWindowCoupling J (S n)) ⟨o, ho n⟩)) b hjoint hpair
        simpa [Function.comp_def] using hc)
      hderiv left_mem_uIcc right_mem_uIcc
    simpa [Real.norm_eq_abs] using hmvt
  have htend : Tendsto (fun n => |Mn n gamma - Mn n beta|) atTop
      (nhds |abigMag G J o gamma h - abigMag G J o beta h|) :=
    ((abig_tendsto_abfaMag_exhaustion G J o gamma h hgamma hh.le hJ hJsupport
        S ho hmonoWindow hcover).sub
      (abig_tendsto_abfaMag_exhaustion G J o beta h hbeta hh.le hJ hJsupport
        S ho hmonoWindow hcover)).abs
  exact le_of_tendsto htend (Filter.Eventually.of_forall hfinite)




theorem abigMag_continuousAt_joint_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 beta h : Real)
    (hJ0 : 0 <= J0) (hbeta : 0 <= beta) (hh : 0 < h)
    (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall b t, 0 <= b -> 0 <= t ->
      forall n (x : S n),
        abigMag G J (x : V) b t <= abigMag G J o b t)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h) := by
  have hfield := abigMag_continuousAt_field_of_exhaustion
    G J o beta h hbeta hh hJ hJsupport S ho hmonoWindow hcover
  rw [Metric.continuousAt_iff] at hfield ⊢
  intro epsilon hepsilon
  obtain ⟨deltaField, hdeltaField, hfieldBound⟩ :=
    hfield (epsilon / 2) (by linarith)
  let deltaBeta : Real := epsilon * h / (4 * (J0 + 1))
  have hdeltaBeta : 0 < deltaBeta := by
    dsimp [deltaBeta]
    positivity
  refine ⟨min (h / 2) (min deltaField deltaBeta), by positivity, ?_⟩
  intro z hz
  have hzbeta : dist z.1 beta <= dist z (beta, h) := by
    rw [Prod.dist_eq]
    exact le_max_left _ _
  have hzfield : dist z.2 h <= dist z (beta, h) := by
    rw [Prod.dist_eq]
    exact le_max_right _ _
  have htclose : dist z.2 h < h / 2 :=
    lt_of_le_of_lt hzfield (lt_of_lt_of_le hz (min_le_left _ _))
  have htpos : 0 < z.2 := by
    rw [Real.dist_eq] at htclose
    have hlower : h - z.2 <= |z.2 - h| := by
      rw [abs_sub_comm]
      exact le_abs_self (h - z.2)
    linarith
  have hfieldClose :
      dist (abigMag G J o beta z.2) (abigMag G J o beta h) < epsilon / 2 := by
    apply hfieldBound
    exact lt_of_le_of_lt hzfield
      (lt_of_lt_of_le hz (le_trans (min_le_right _ _) (min_le_left _ _)))
  let b : Real := max z.1 0
  have hb0 : 0 <= b := le_max_right _ _
  have hbclose : |b - beta| <= dist z (beta, h) := by
    calc
      |b - beta| = |max z.1 0 - max beta 0| := by
        rw [max_eq_left hbeta]
      _ <= |z.1 - beta| := abs_max_sub_max_le_abs _ _ _
      _ = dist z.1 beta := by rw [Real.dist_eq]
      _ <= dist z (beta, h) := hzbeta
  have hbetaLip := abigMag_beta_lipschitz_of_exhaustion
    G J o J0 beta b z.2 hJ0 hbeta hb0 htpos hJ hJsupport
      S ho hrow hInfiniteTarget hmonoWindow hcover
  have hcoef : J0 / z.2 <= 2 * J0 / h := by
    have hhalf : h <= 2 * z.2 := by
      rw [Real.dist_eq] at htclose
      have hlower : h - z.2 <= |z.2 - h| := by
        rw [abs_sub_comm]
        exact le_abs_self (h - z.2)
      linarith
    rw [div_le_div_iff₀ htpos hh]
    nlinarith
  have hbetaClose :
      |abigMag G J o z.1 z.2 - abigMag G J o beta z.2| < epsilon / 2 := by
    rw [abigMag_eq_max_beta_zero G J o z.1 z.2 hJ]
    calc
      |abigMag G J o b z.2 - abigMag G J o beta z.2| <=
          (J0 / z.2) * |b - beta| := hbetaLip
      _ <= (2 * J0 / h) * dist z (beta, h) := by
        exact mul_le_mul hcoef hbclose (abs_nonneg _) (by positivity)
      _ <= (2 * J0 / h) * deltaBeta := by
        apply mul_le_mul_of_nonneg_left
        · exact le_of_lt (lt_of_lt_of_le hz
            (le_trans (min_le_right _ _) (min_le_right _ _)))
        · positivity
      _ < epsilon / 2 := by
        dsimp [deltaBeta]
        have hratio : J0 / (J0 + 1) < 1 := by
          apply (div_lt_one (by linarith)).mpr
          linarith
        have hratio0 : 0 <= J0 / (J0 + 1) := div_nonneg hJ0 (by linarith)
        field_simp
        nlinarith
  rw [Real.dist_eq] at hfieldClose ⊢
  exact (abs_sub_le (abigMag G J o z.1 z.2)
    (abigMag G J o beta z.2) (abigMag G J o beta h)).trans_lt (by
      linarith)



theorem abigMag_deriv_field_nonneg_of_monotone
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (hh : 0 < h)
    (hmono : MonotoneOn (fun t => abigMag G J o beta t) (Ici 0))
    (hdiff : DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
    0 <= deriv (fun t => abigMag G J o beta t) h := by
  apply ge_of_tendsto hdiff.hasDerivAt.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  change 0 < t at ht
  have hinc : abigMag G J o beta h <= abigMag G J o beta (h + t) :=
    hmono (mem_Ici.mpr hh.le) (mem_Ici.mpr (by linarith [hh, ht]))
      (by linarith [ht])
  exact mul_nonneg (inv_nonneg.mpr ht.le) (sub_nonneg.mpr hinc)

omit [Countable V] in


theorem abig_finiteMag_le [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    (T : Finset (Option V)) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) <=
      abigMag G J o beta h := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact abig_connEvent_mono_set (withGhost G) (Set.subset_univ _)
    (some o) none

omit [Countable V] in

theorem abig_finiteMag_mono [DecidableEq V]
    (G : SimpleGraph V) (J : Sym2 V -> Real) (o : V) (beta h : Real)
    {S T : Finset (Option V)} (hST : S ⊆ T) :
    (abigMeasure J beta h).real
        (connEvent (withGhost G) (S : Set (Option V)) (some o) {none}) <=
      (abigMeasure J beta h).real
        (connEvent (withGhost G) (T : Set (Option V)) (some o) {none}) := by
  apply measureReal_mono (h₂ := measure_ne_top _ _)
  exact abig_connEvent_mono_set (withGhost G) hST (some o) none




theorem abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h ->
      forall n (x : S n),
        abigMag G J (x : V) beta h <= abigMag G J o beta h)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hcontLimit : forall beta h, 0 <= beta -> 0 < h ->
      ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h))
    (hfieldDiffLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  let Mn : Nat -> Real -> Real -> Real := fun n beta h =>
    abfaMag (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
      ⟨o, ho n⟩ beta h
  let Cn : Nat -> Real -> Real -> Real := fun n beta h =>
    abigWindowEnvelope G J (S n) ⟨o, ho n⟩ beta h
  intro beta hbeta h hh
  have hmonoLimit := abigMag_monotoneOn_field_of_exhaustion
    G J o beta hbeta hJ hJsupport S ho hmonoWindow hcover
  have hfieldDiff := hfieldDiffLimit beta h hbeta hh
  have hfieldNN := abigMag_deriv_field_nonneg_of_monotone
    G J o beta h hh hmonoLimit hfieldDiff
  apply abtp_inequality_at_of_fieldDifferentiable_physical_envelope
    Mn Cn (abigMag G J o) J0 beta h hJ0 hbeta hh
    (abigMag_nonneg G J o beta h)
  · intro n b t hb ht
    simpa [Mn, Cn, mul_assoc] using
      (abig_window_aizenmanBarsky_finiteEnvelope
        G J (S n) ⟨o, ho n⟩ b t J0 hb ht hJ (hrow n))
  · intro n b t hb ht
    apply abfa_deriv_field_nonneg
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ b t
    · intro e he
      induction e using Sym2.inductionOn with
      | _ x y => simpa using hJ s((x : V), (y : V))
    · exact hb
    · exact ht
  · intro n t ht
    exact abigWindowEnvelope_monotoneOn_beta
      G J (S n) ⟨o, ho n⟩ t hJ ht
  · intro n b hb
    exact abigWindowEnvelope_monotoneOn_field
      G J (S n) ⟨o, ho n⟩ b hJ hb
  · intro n b t hb ht
    exact abigWindowEnvelope_le_mag G J (S n) ⟨o, ho n⟩ b t
      hb ht hJ hJsupport (hInfiniteTarget b t hb ht n)
  · intro b t hb ht
    exact abig_tendsto_abfaMag_exhaustion G J o b t hb ht hJ hJsupport
      S ho hmonoWindow hcover
  · exact hcontLimit beta h hbeta hh
  · intro n b t
    exact abfa_differentiableAt_mag_joint
      (abigWindowGraph G (S n)) (abigWindowCoupling J (S n))
        ⟨o, ho n⟩ b t
  · exact hfieldDiff
  · exact hfieldNN




theorem abig_aizenmanBarskyPhysical_unconditional_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h ->
      forall n (x : S n),
        abigMag G J (x : V) beta h <= abigMag G J o beta h)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover
  · intro beta h hbeta hh
    exact abigMag_continuousAt_joint_of_exhaustion
      G J o J0 beta h hJ0 hbeta hh hJ hJsupport S ho hrow
        hInfiniteTarget hmonoWindow hcover
  · intro beta h hbeta hh
    exact abigMag_differentiableAt_field_of_exhaustion
      G J o beta h hbeta hh hJ hJsupport S ho hmonoWindow hcover




theorem abig_aizenmanBarskyPhysical_of_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hrow : forall n (x : S n),
      abcrIncidentCoupling (abigWindowGraph G (S n))
        (abigWindowCoupling J (S n)) x <= J0)
    (hInfiniteTarget : forall beta h, 0 <= beta -> 0 <= h ->
      forall n (x : S n),
        abigMag G J (x : V) beta h <= abigMag G J o beta h)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho hrow hInfiniteTarget hmonoWindow hcover
  · intro beta h hbeta hh
    exact (hjointLimit beta h hbeta hh).continuousAt
  · intro beta h hbeta hh
    have hjoint := hjointLimit beta h hbeta hh
    have hline : DifferentiableAt Real (fun t : Real => (beta, t)) h :=
      (differentiableAt_const beta).prodMk differentiableAt_id
    simpa [Function.comp_def, Function.uncurry] using hjoint.comp h hline



theorem abig_aizenmanBarskyPhysical_of_tsum_transitive_fieldRegular
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hcontLimit : forall beta h, 0 <= beta -> 0 < h ->
      ContinuousAt (Function.uncurry (abigMag G J o)) (beta, h))
    (hfieldDiffLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (fun t => abigMag G J o beta t) h) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_fieldRegular_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho
  · intro n x
    exact abigWindow_incidentCoupling_le G J J0
      (abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow) (S n) x
  · intro beta h hbeta hh n x
    exact le_of_eq (abigMag_eq_of_transitive G J o beta h move hmove
      hG hJinv (fun k => abigGhostWindow (S k)) hcover (x : V))
  · exact hmonoWindow
  · exact hcover
  · exact hcontLimit
  · exact hfieldDiffLimit



theorem abig_aizenmanBarskyPhysical_of_tsum_transitive_unconditional
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_unconditional_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho
  · intro n x
    exact abigWindow_incidentCoupling_le G J J0
      (abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow) (S n) x
  · intro beta h hbeta hh n x
    exact le_of_eq (abigMag_eq_of_transitive G J o beta h move hmove
      hG hJinv (fun k => abigGhostWindow (S k)) hcover (x : V))
  · exact hmonoWindow
  · exact hcover




theorem abig_aizenmanBarskyPhysical_of_transitive_exhaustion [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hrow : abigUniformFiniteRowBound G J J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_exhaustion
    G J o J0 hJ0 hJ hJsupport S ho
  · intro n x
    exact abigWindow_incidentCoupling_le G J J0 hrow (S n) x
  · intro beta h hbeta hh n x
    exact le_of_eq (abigMag_eq_of_transitive G J o beta h move hmove
      hG hJinv (fun k => abigGhostWindow (S k)) hcover (x : V))
  · exact hmonoWindow
  · exact hcover
  · exact hjointLimit



theorem abig_aizenmanBarskyPhysical_of_tsum_transitive_exhaustion
    [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (o : V) (J0 : Real)
    (hJ0 : 0 <= J0) (hJ : forall e, 0 <= J e)
    (hJsupport : forall x y, ¬ G.Adj x y -> J s(x, y) = 0)
    (hsum : forall x, Summable (fun y =>
      if G.Adj x y then J s(x, y) else 0))
    (hrow : forall x, (∑' y,
      if G.Adj x y then J s(x, y) else 0) <= J0)
    (move : V -> (V ≃ V)) (hmove : forall x, move x o = x)
    (hG : forall x u v, G.Adj (move x u) (move x v) <-> G.Adj u v)
    (hJinv : forall x u v, J s(move x u, move x v) = J s(u, v))
    (S : Nat -> Finset V) (ho : forall n, o ∈ S n)
    (hmonoWindow : Monotone (fun n => abigGhostWindow (S n)))
    (hcover : forall F : Finset (Option V),
      exists n, F ⊆ abigGhostWindow (S n))
    (hjointLimit : forall beta h, 0 <= beta -> 0 < h ->
      DifferentiableAt Real (Function.uncurry (abigMag G J o)) (beta, h)) :
    AizenmanBarskyInequalityPhysical (abigMag G J o) J0 := by
  apply abig_aizenmanBarskyPhysical_of_transitive_exhaustion
    G J o J0 hJ0 hJ hJsupport
    (abigUniformFiniteRowBound_of_tsum G J J0 hJ hsum hrow)
    move hmove hG hJinv S ho hmonoWindow hcover hjointLimit



theorem abig_ghost_edge_prob (J : Sym2 V -> Real) (beta h : Real)
    (hh : 0 <= h) (x : V) :
    (abigMeasure J beta h).real
        {omega | omega s(some x, none) = true} = qField h := by
  rw [abig_coord_true_prob, abigParam_some_none]
  exact Real.coe_toNNReal _ (qField_mem h hh).1



theorem abig_physical_edge_prob (J : Sym2 V -> Real) (beta h : Real)
    (hbeta : 0 <= beta) {x y : V} (hJ : 0 <= J s(x, y)) :
    (abigMeasure J beta h).real
        {omega | omega s(some x, some y) = true} = pBeta (J s(x, y)) beta := by
  rw [abig_coord_true_prob, abigParam_some_some]
  exact Real.coe_toNNReal _ (pBeta_nonneg (mul_nonneg hbeta hJ))

end Marginals

end Sharpness
end StatMech
