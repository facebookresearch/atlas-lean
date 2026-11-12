/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.FreeEvenSpinMixing
import Code.FrontierB.PlusParityPatternMixing

open Filter MeasureTheory Set Topology
open scoped BigOperators ENNReal symmDiff

namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

private theorem even_card_symmDiff {V : Type*} [DecidableEq V]
    (A B : Finset V) (hA : Even A.card) (hB : Even B.card) :
    Even (A ∆ B).card := by
  have hdisj : Disjoint (A \ B) (B \ A) := by
    rw [Finset.disjoint_left]
    intro x hxA hxB
    rw [Finset.mem_sdiff] at hxA hxB
    exact hxB.2 hxA.1
  have hcard : (A ∆ B).card = (A \ B).card + (B \ A).card := by
    rw [show A ∆ B = (A \ B) ∪ (B \ A) by
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_union, Finset.mem_sdiff]
      ]
    exact Finset.card_union_of_disjoint hdisj
  rcases hA with ⟨a, ha⟩
  rcases hB with ⟨b, hb⟩
  have hAcard := Finset.card_sdiff_add_card_inter A B
  have hBcard := Finset.card_sdiff_add_card_inter B A
  rw [Finset.inter_comm B A] at hBcard
  refine ⟨a + b - (A ∩ B).card, ?_⟩
  omega

theorem edgeBoundary_card_even {V : Type*} [DecidableEq V]
    (F : Finset (Sym2 V)) (hF : ∀ e ∈ F, ¬ e.IsDiag) :
    Even (edgeBoundary F).card := by
  classical
  induction F using Finset.induction with
  | empty => simp [edgeBoundary]
  | @insert e F he ih =>
      have hediag : ¬ e.IsDiag := hF e (Finset.mem_insert_self e F)
      have hF' : ∀ f ∈ F, ¬ f.IsDiag :=
        fun f hf => hF f (Finset.mem_insert_of_mem hf)
      have hedge : Even e.toFinset.card := by
        induction e using Sym2.inductionOn with
        | _ x y =>
            have hxy : x ≠ y := by simpa [Sym2.IsDiag] using hediag
            rw [Sym2.toFinset_mk_eq, Finset.card_pair hxy]
            exact even_two
      rw [edgeBoundary, Finset.fold_insert he]
      exact even_card_symmDiff _ _ hedge (ih hF')

theorem infiniteFreeCurrentMeasure_parityAvoid_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (F : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityAvoidCylinder F) =
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega)
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
          Real.cosh beta ^ F.card := by
  rw [Measure.real,
    infiniteFreeCurrentMeasure_parityAvoid_eq d beta hbeta F hF,
    ENNReal.toReal_ofReal]
  positivity



theorem infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (F F' : Finset (Sym2 (Site d)))
    (hF : (↑F : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hF' : (↑F' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint F (currentShiftFinset g F')) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityAvoidCylinder F ∩
          (currentShift g) ⁻¹' currentParityAvoidCylinder F') =
      (∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega))
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
        (Real.cosh beta ^ F.card * Real.cosh beta ^ F'.card) := by
  let G := currentShiftFinset g F'
  have hG : (↑G : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet :=
    currentShiftFinset_lattice d g F' hF'
  have hFG : (↑(F ∪ G) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
    intro e he
    change e ∈ F ∪ G at he
    exact (Finset.mem_union.mp he).elim (fun h => hF h) (fun h => hG h)
  rw [preimage_currentParityAvoidCylinder_currentShift,
    currentParityAvoidCylinder_inter,
    infiniteFreeCurrentMeasure_parityAvoid_real_eq hbeta (F ∪ G) hFG]
  have hcard : (F ∪ G).card = F.card + F'.card := by
    rw [Finset.card_union_of_disjoint hdisj]
    congr 1
    dsimp [G, currentShiftFinset]
    rw [Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]
  have hint (omega : ConfigSpace (Site d)) :
      Real.exp (-beta * edgeSpinSum (F ∪ G) omega) =
        Real.exp (-beta * edgeSpinSum F omega) *
          Real.exp (-beta * edgeSpinSum F' (shift g omega)) := by
    rw [edgeSpinSum_union hdisj, edgeSpinSum_shift]
    rw [show -beta * (edgeSpinSum F omega + edgeSpinSum G omega) =
        -beta * edgeSpinSum F omega + -beta * edgeSpinSum G omega by ring,
      Real.exp_add]
  rw [show (∫ omega, Real.exp (-beta * edgeSpinSum (F ∪ G) omega)
      ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) =
      ∫ omega, Real.exp (-beta * edgeSpinSum F omega) *
        Real.exp (-beta * edgeSpinSum F' (shift g omega))
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) by
      apply integral_congr_ae
      filter_upwards with omega
      exact hint omega]
  rw [hcard, pow_add]



theorem infiniteFreeCurrentMeasure_parityPattern_real_eq_integral {d : Nat}
    {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd) =
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [currentParityPattern_real_eq_avoid_sum]
  unfold plusParityPatternSpinPolynomial
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [integral_const_mul]
    rw [infiniteFreeCurrentMeasure_parityAvoid_real_eq hbeta T]
    · ring
    · intro e he
      exact hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
  · intro T hT
    apply Integrable.const_mul
    have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
      intro e he
      exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
        (hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he))
    have hexp : (fun omega : ConfigSpace (Site d) =>
        Real.exp (-beta * edgeSpinSum T omega)) =
        fun omega => ∑ U ∈ T.powerset,
          edgeExpansionCoeff beta T U * spinProd (edgeBoundary (T \ U)) omega := by
      funext omega
      exact exp_neg_edgeSpinSum_eq_spinProd_sum beta T hTdiag omega
    rw [hexp]
    apply integrable_finsetSum
    intro U hU
    exact ((spinProdBCF d (edgeBoundary (T \ U))).integrable
      (freeState d beta 0 : Measure (ConfigSpace (Site d)))).const_mul _



theorem infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral
    {d : Nat} {beta : Real} (hbeta : 0 < beta)
    (g : Multiplicative (Site d))
    (S S' : Finset (Sym2 (Site d))) (odd : ↑S -> Bool) (odd' : ↑S' -> Bool)
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hS' : (↑S' : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (hdisj : Disjoint S (currentShiftFinset g S')) :
    (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
        (currentParityPatternCylinder S odd ∩
          (currentShift g) ⁻¹' currentParityPatternCylinder S' odd') =
      ∫ omega, plusParityPatternSpinPolynomial beta S odd omega *
        plusParityPatternSpinPolynomial beta S' odd' (shift g omega)
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  rw [currentParityPattern_inter_shift_real_eq_avoid_sum]
  have hTdiag (T : Finset (Sym2 (Site d))) (hT : T ∈ S.powerset) :
      ∀ e ∈ T, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
      (hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he))
  have hUdiag (U : Finset (Sym2 (Site d))) (hU : U ∈ S'.powerset) :
      ∀ e ∈ U, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet
      (hS' (Finset.mem_of_subset (Finset.mem_powerset.mp hU) he))
  have hjoint (T : Finset (Sym2 (Site d))) (hT : T ∈ S.powerset)
      (U : Finset (Sym2 (Site d))) (hU : U ∈ S'.powerset) :
      (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U) =
        (∫ omega, Real.exp (-beta * edgeSpinSum T omega) *
            Real.exp (-beta * edgeSpinSum U (shift g omega))
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
          (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card) := by
    apply infiniteFreeCurrentMeasure_parityAvoid_inter_shift_real_eq
      hbeta g T U
    · intro e he
      exact hS (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
    · intro e he
      exact hS' (Finset.mem_of_subset (Finset.mem_powerset.mp hU) he)
    · apply hdisj.mono (Finset.mem_powerset.mp hT)
      unfold currentShiftFinset
      exact Finset.image_mono (fun e => g⁻¹ • e)
        (Finset.mem_powerset.mp hU)
  rw [show (∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
      currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
        (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
          (currentParityAvoidCylinder T ∩
            (currentShift g) ⁻¹' currentParityAvoidCylinder U)) =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
      currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U *
        ((∫ omega, Real.exp (-beta * edgeSpinSum T omega) *
            Real.exp (-beta * edgeSpinSum U (shift g omega))
          ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
          (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card)) by
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro U hU
    rw [hjoint T hT U hU]]
  symm
  unfold plusParityPatternSpinPolynomial
  have hpoint (omega : ConfigSpace (Site d)) :
      (∑ T ∈ S.powerset, currentParityTraceCoeff S odd T *
          Real.cosh beta ^ T.card * Real.exp (-beta * edgeSpinSum T omega)) *
        (∑ U ∈ S'.powerset, currentParityTraceCoeff S' odd' U *
          Real.cosh beta ^ U.card *
            Real.exp (-beta * edgeSpinSum U (shift g omega))) =
      ∑ T ∈ S.powerset, ∑ U ∈ S'.powerset,
        (currentParityTraceCoeff S odd T * currentParityTraceCoeff S' odd' U) *
          ((Real.exp (-beta * edgeSpinSum T omega) *
              Real.exp (-beta * edgeSpinSum U (shift g omega))) *
            (Real.cosh beta ^ T.card * Real.cosh beta ^ U.card)) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro T hT
    apply Finset.sum_congr rfl
    intro U hU
    ring
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro T hT
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro U hU
      rw [integral_const_mul, integral_mul_const]
    · intro U hU
      apply Integrable.const_mul
      apply Integrable.mul_const
      exact integrable_exp_neg_edgeSpinSum_mul_shift
        (freeState d beta 0 : Measure (ConfigSpace (Site d))) beta g T U
          (hTdiag T hT) (hUdiag U hU)
  · intro T hT
    apply integrable_finsetSum
    intro U hU
    apply Integrable.const_mul
    apply Integrable.mul_const
    exact integrable_exp_neg_edgeSpinSum_mul_shift
      (freeState d beta 0 : Measure (ConfigSpace (Site d))) beta g T U
        (hTdiag T hT) (hUdiag U hU)

abbrev FreeParityExpansionIndex (d : Nat) :=
  Sigma fun _ : Finset (Sym2 (Site d)) => Finset (Sym2 (Site d))

noncomputable def freeParityExpansionIndices {d : Nat}
    (S : Finset (Sym2 (Site d))) : Finset (FreeParityExpansionIndex d) :=
  S.powerset.sigma fun T => T.powerset

noncomputable def freeParityExpansionCoeff {d : Nat} (beta : Real)
    (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (i : FreeParityExpansionIndex d) : Real :=
  currentParityTraceCoeff S odd i.1 * Real.cosh beta ^ i.1.card *
    edgeExpansionCoeff beta i.1 i.2

noncomputable def freeParityExpansionSupport {d : Nat}
    (i : FreeParityExpansionIndex d) : Finset (Site d) :=
  edgeBoundary (i.1 \ i.2)

theorem plusParityPatternSpinPolynomial_eq_freeEvenExpansion {d : Nat}
    (beta : Real) (S : Finset (Sym2 (Site d))) (odd : ↑S -> Bool)
    (hS : ∀ e ∈ S, ¬ e.IsDiag) (omega : ConfigSpace (Site d)) :
    plusParityPatternSpinPolynomial beta S odd omega =
      ∑ i ∈ freeParityExpansionIndices S,
        freeParityExpansionCoeff beta S odd i *
          spinProd (freeParityExpansionSupport i) omega := by
  unfold plusParityPatternSpinPolynomial freeParityExpansionIndices
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro T hT
  have hTdiag : ∀ e ∈ T, ¬ e.IsDiag := by
    intro e he
    exact hS e (Finset.mem_of_subset (Finset.mem_powerset.mp hT) he)
  rw [exp_neg_edgeSpinSum_eq_spinProd_sum beta T hTdiag omega,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [freeParityExpansionCoeff, freeParityExpansionSupport]
  ring

private theorem integrable_spinProd_mul_shift
    (mu : Measure (ConfigSpace (Site d))) [IsFiniteMeasure mu]
    (g : Multiplicative (Site d)) (A B : Finset (Site d)) :
    Integrable (fun omega => spinProd A omega * spinProd B (shift g omega)) mu := by
  have hfun : (fun omega : ConfigSpace (Site d) =>
      spinProd A omega * spinProd B (shift g omega)) =
      fun omega => spinProd (A ∆ B.image fun x => g⁻¹ • x) omega := by
    funext omega
    rw [spinProd_shift, spinProd_mul_self]
  rw [hfun]
  exact (spinProdBCF d (A ∆ B.image fun x => g⁻¹ • x)).integrable mu



theorem infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K : Nat)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Bool))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ k : Nat, K ≤ k ∧
      Disjoint S (currentShiftFinset (FK.freeAxisTranslationPower hd k) S) ∧
      ∀ odd ∈ patterns, ∀ odd' ∈ patterns,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S odd ∩
              (currentShift (FK.freeAxisTranslationPower hd k)) ⁻¹'
                currentParityPatternCylinder S odd') -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd')) < epsilon := by
  classical
  let I := freeParityExpansionIndices S
  let support : FreeParityExpansionIndex d -> Finset (Site d) :=
    freeParityExpansionSupport
  let expansionSupports : Finset (Finset (Site d)) := I.image support
  let edgeSupports : Finset (Finset (Site d)) := S.image Sym2.toFinset
  let supports := expansionSupports ∪ edgeSupports
  let coeff : (↑S -> Bool) -> FreeParityExpansionIndex d -> Real :=
    fun odd i => freeParityExpansionCoeff beta S odd i
  let coeffs : Finset (FreeParityExpansionIndex d -> Real) := patterns.image coeff
  let M := ∑ c ∈ coeffs, ∑ i ∈ I, |c i|
  have hM : 0 ≤ M := Finset.sum_nonneg fun c hc =>
    Finset.sum_nonneg fun i hi => abs_nonneg _
  let delta := epsilon / (M * M + 1)
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  have hSdiag : ∀ e ∈ S, ¬ e.IsDiag := by
    intro e he
    exact (hypercubicLattice d).not_isDiag_of_mem_edgeSet (hS he)
  have hsupportEven : ∀ A ∈ supports, Even A.card := by
    intro A hA
    rcases Finset.mem_union.mp hA with hA | hA
    · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hA
      change i ∈ freeParityExpansionIndices S at hi
      rw [freeParityExpansionIndices, Finset.mem_sigma] at hi
      apply edgeBoundary_card_even
      intro e he
      exact hSdiag e (Finset.mem_of_subset
        (Finset.mem_powerset.mp hi.1)
        (Finset.mem_of_subset (Finset.sdiff_subset) he))
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hA
      induction e using Sym2.inductionOn with
      | _ x y =>
          have hxy : x ≠ y := by
            simpa [Sym2.IsDiag] using hSdiag s(x, y) he
          rw [Sym2.toFinset_mk_eq, Finset.card_pair hxy]
          exact even_two
  obtain ⟨k, hkK, hparity⟩ :=
    freeInfiniteVolume_evenParity_family_pairMixing_after
      hd hbeta K supports hsupportEven delta hdelta
  let g := FK.freeAxisTranslationPower hd k
  change ∀ A ∈ supports, ∀ B ∈ supports,
    Disjoint A (B.image fun x => g⁻¹ • x) ∧
      abs ((freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (allClustersEvenEvent (hypercubicLattice d)
              (A ∪ B.image fun x => g⁻¹ • x)) -
        (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (allClustersEvenEvent (hypercubicLattice d) A) *
        (freeInfiniteVolume d
          (p := 1 - Real.exp (-2 * beta)) (q := 2)
          (by
            apply sub_pos.mpr
            rw [Real.exp_lt_one_iff]
            linarith)
          (by linarith [Real.exp_pos (-2 * beta)])
          (by norm_num : (0 : Real) < 2) : Measure _).real
            (allClustersEvenEvent (hypercubicLattice d) B)) < delta at hparity
  have hindexDisj : ∀ i ∈ I, ∀ j ∈ I,
      Disjoint (support i) ((support j).image fun x => g⁻¹ • x) := by
    intro i hi j hj
    exact (hparity (support i)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
      (support j)
      (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩))).1
  have hedgeDisj : Disjoint S (currentShiftFinset g S) := by
    rw [Finset.disjoint_left]
    intro e heS heShift
    rw [currentShiftFinset, Finset.mem_image] at heShift
    obtain ⟨e', heS', heq⟩ := heShift
    have hpair := (hparity e.toFinset
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, heS, rfl⟩))
      e'.toFinset
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e', heS', rfl⟩))).1
    have hx : g⁻¹ • e'.out.1 ∈ e := by
      have hx' : g⁻¹ • e'.out.1 ∈ g⁻¹ • e' := by
        change g⁻¹ • e'.out.1 ∈ Sym2.map (fun x => g⁻¹ • x) e'
        exact Sym2.mem_map.mpr ⟨e'.out.1, Sym2.out_fst_mem e', rfl⟩
      rwa [heq] at hx'
    exact (Finset.disjoint_left.mp hpair
      (by simpa only [Sym2.mem_toFinset] using hx))
      (Finset.mem_image.mpr ⟨e'.out.1,
        by simpa only [Sym2.mem_toFinset] using Sym2.out_fst_mem e', rfl⟩)
  let spinMu := (freeState d beta 0 : Measure (ConfigSpace (Site d)))
  have hgood : ∀ i ∈ I, ∀ j ∈ I,
      abs ((∫ omega, spinProd (support i) omega *
          spinProd (support j) (shift g omega) ∂spinMu) -
        (∫ omega, spinProd (support i) omega ∂spinMu) *
          (∫ omega, spinProd (support j) omega ∂spinMu)) < delta := by
    intro i hi j hj
    have hiMem : support i ∈ supports :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hjMem : support j ∈ supports :=
      Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
    have hbase := (hparity (support i) hiMem (support j) hjMem).2
    have hiEven := hsupportEven (support i) hiMem
    have hjEven := hsupportEven (support j) hjMem
    have hdisj := hindexDisj i hi j hj
    have hunionEven : Even
        (support i ∪ (support j).image fun x => g⁻¹ • x).card := by
      rw [Finset.card_union_of_disjoint hdisj,
        Finset.card_image_of_injective _ (MulAction.injective g⁻¹)]
      exact hiEven.add hjEven
    rw [← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
        d beta hbeta hd _ hunionEven,
      ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
        d beta hbeta hd _ hiEven,
      ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
        d beta hbeta hd _ hjEven] at hbase
    have hjoint :
        (∫ omega, spinProd (support i) omega *
          spinProd (support j) (shift g omega) ∂spinMu) =
        ∫ omega, spinProd
          (support i ∪ (support j).image fun x => g⁻¹ • x) omega
            ∂spinMu := by
      apply integral_congr_ae
      filter_upwards with omega
      rw [spinProd_shift, spinProd_mul_self, Finset.symmDiff_eq_union hdisj]
    rw [hjoint]
    simpa only [spinMu] using hbase
  refine ⟨k, hkK, ?_⟩
  change Disjoint S (currentShiftFinset g S) ∧ _
  refine ⟨hedgeDisj, ?_⟩
  intro odd hodd odd' hodd'
  have hc : coeff odd ∈ coeffs := Finset.mem_image.mpr ⟨odd, hodd, rfl⟩
  have hc' : coeff odd' ∈ coeffs := Finset.mem_image.mpr ⟨odd', hodd', rfl⟩
  have hcM : (∑ i ∈ I, |coeff odd i|) ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun i hi => abs_nonneg (c i)) hc
  have hc'M : (∑ i ∈ I, |coeff odd' i|) ≤ M := by
    dsimp [M]
    exact Finset.single_le_sum
      (fun c hc => Finset.sum_nonneg fun i hi => abs_nonneg (c i)) hc'
  have hleftPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ I, coeff odd i * spinProd (support i) omega) =
        plusParityPatternSpinPolynomial beta S odd omega := by
    exact (plusParityPatternSpinPolynomial_eq_freeEvenExpansion
      beta S odd hSdiag omega).symm
  have hrightPoint (omega : ConfigSpace (Site d)) :
      (∑ i ∈ I, coeff odd' i * spinProd (support i) omega) =
        plusParityPatternSpinPolynomial beta S odd' omega := by
    exact (plusParityPatternSpinPolynomial_eq_freeEvenExpansion
      beta S odd' hSdiag omega).symm
  rw [infiniteFreeCurrentMeasure_parityPattern_inter_shift_real_eq_integral
      hbeta g S S odd odd' hS hS hedgeDisj,
    infiniteFreeCurrentMeasure_parityPattern_real_eq_integral hbeta S odd hS,
    infiniteFreeCurrentMeasure_parityPattern_real_eq_integral hbeta S odd' hS]
  simp_rw [← hleftPoint, ← hrightPoint]
  have hint :
      (∫ omega, (∑ i ∈ I, coeff odd i * spinProd (support i) omega) *
          (∑ j ∈ I, coeff odd' j * spinProd (support j) (shift g omega))
        ∂spinMu) =
      ∑ i ∈ I, ∑ j ∈ I, coeff odd i * coeff odd' j *
        ∫ omega, spinProd (support i) omega *
          spinProd (support j) (shift g omega) ∂spinMu := by
    simp_rw [Finset.sum_mul_sum]
    have hpoint (i j : FreeParityExpansionIndex d)
        (omega : ConfigSpace (Site d)) :
        (coeff odd i * spinProd (support i) omega) *
          (coeff odd' j * spinProd (support j) (shift g omega)) =
        (coeff odd i * coeff odd' j) *
          (spinProd (support i) omega *
            spinProd (support j) (shift g omega)) := by ring
    simp_rw [hpoint]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul]
      · intro j hj
        exact (integrable_spinProd_mul_shift spinMu g (support i) (support j)).const_mul _
    · intro i hi
      apply integrable_finsetSum
      intro j hj
      exact (integrable_spinProd_mul_shift spinMu g (support i) (support j)).const_mul _
  rw [hint, integral_finsetSum, integral_finsetSum, Finset.sum_mul_sum,
    ← Finset.sum_sub_distrib]
  · simp_rw [integral_const_mul]
    have hdiff (i : FreeParityExpansionIndex d) :
        (∑ j ∈ I, coeff odd i * coeff odd' j *
            ∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
          ∑ j ∈ I,
            (coeff odd i * ∫ omega, spinProd (support i) omega ∂spinMu) *
              (coeff odd' j * ∫ omega, spinProd (support j) omega ∂spinMu) =
          ∑ j ∈ I, coeff odd i * coeff odd' j *
            ((∫ omega, spinProd (support i) omega *
                spinProd (support j) (shift g omega) ∂spinMu) -
              (∫ omega, spinProd (support i) omega ∂spinMu) *
                (∫ omega, spinProd (support j) omega ∂spinMu)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change abs (∑ i ∈ I,
      ((∑ j ∈ I, coeff odd i * coeff odd' j *
          ∫ omega, spinProd (support i) omega *
            spinProd (support j) (shift g omega) ∂spinMu) -
        ∑ j ∈ I,
          (coeff odd i * ∫ omega, spinProd (support i) omega ∂spinMu) *
            (coeff odd' j * ∫ omega, spinProd (support j) omega ∂spinMu))) <
      epsilon
    rw [show (∑ i ∈ I,
        ((∑ j ∈ I, coeff odd i * coeff odd' j *
            ∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
          ∑ j ∈ I,
            (coeff odd i * ∫ omega, spinProd (support i) omega ∂spinMu) *
              (coeff odd' j * ∫ omega, spinProd (support j) omega ∂spinMu))) =
        ∑ i ∈ I, ∑ j ∈ I, coeff odd i * coeff odd' j *
          ((∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
            (∫ omega, spinProd (support i) omega ∂spinMu) *
              (∫ omega, spinProd (support j) omega ∂spinMu)) by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdiff i]
    calc
      abs (∑ i ∈ I, ∑ j ∈ I, coeff odd i * coeff odd' j *
          ((∫ omega, spinProd (support i) omega *
              spinProd (support j) (shift g omega) ∂spinMu) -
            (∫ omega, spinProd (support i) omega ∂spinMu) *
              (∫ omega, spinProd (support j) omega ∂spinMu))) ≤
          ∑ i ∈ I, ∑ j ∈ I, |coeff odd i| * |coeff odd' j| * delta := by
        calc
          _ ≤ ∑ i ∈ I, ∑ j ∈ I, abs (coeff odd i * coeff odd' j *
              ((∫ omega, spinProd (support i) omega *
                  spinProd (support j) (shift g omega) ∂spinMu) -
                (∫ omega, spinProd (support i) omega ∂spinMu) *
                  (∫ omega, spinProd (support j) omega ∂spinMu))) := by
            apply (Finset.abs_sum_le_sum_abs _ _).trans
            apply Finset.sum_le_sum
            intro i hi
            exact Finset.abs_sum_le_sum_abs _ _
          _ ≤ _ := by
            apply Finset.sum_le_sum
            intro i hi
            apply Finset.sum_le_sum
            intro j hj
            rw [abs_mul, abs_mul]
            apply mul_le_mul_of_nonneg_left _
              (mul_nonneg (abs_nonneg _) (abs_nonneg _))
            exact (hgood i hi j hj).le
      _ = (∑ i ∈ I, |coeff odd i|) *
          (∑ j ∈ I, |coeff odd' j|) * delta := by
        rw [Finset.sum_mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.sum_mul]
      _ ≤ (M * M) * delta := by
        apply mul_le_mul_of_nonneg_right _ hdelta.le
        exact mul_le_mul hcM hc'M
          (Finset.sum_nonneg fun i hi => abs_nonneg _) hM
      _ < epsilon := by
        dsimp [delta]
        have hne : M * M + 1 ≠ 0 := by positivity
        have hpos : 0 < epsilon / (M * M + 1) := by positivity
        calc
          M * M * (epsilon / (M * M + 1)) <
              (M * M + 1) * (epsilon / (M * M + 1)) :=
            mul_lt_mul_of_pos_right (by linarith) hpos
          _ = epsilon := mul_div_cancel₀ epsilon hne
  · intro i hi
    exact (spinProdBCF d (support i)).integrable spinMu |>.const_mul _
  · intro i hi
    exact (spinProdBCF d (support i)).integrable spinMu |>.const_mul _

theorem infiniteFreeCurrentMeasure_parityPattern_family_pairMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (S : Finset (Sym2 (Site d)))
    (hS : (↑S : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet)
    (patterns : Finset (↑S -> Bool))
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    ∃ g : Multiplicative (Site d),
      Disjoint S (currentShiftFinset g S) ∧
      ∀ odd ∈ patterns, ∀ odd' ∈ patterns,
        abs ((infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
            (currentParityPatternCylinder S odd ∩
              (currentShift g) ⁻¹' currentParityPatternCylinder S odd') -
          (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd) *
            (infiniteFreeCurrentMeasure d beta hbeta.le : Measure _).real
              (currentParityPatternCylinder S odd')) < epsilon := by
  obtain ⟨k, hk, hdisj, hmix⟩ :=
    infiniteFreeCurrentMeasure_parityPattern_family_pairMixing_after
      hd hbeta 0 S hS patterns epsilon hepsilon
  exact ⟨FK.freeAxisTranslationPower hd k, hdisj, hmix⟩

end StatMech.FrontierB
