/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierB.PlusCurrentFamilyMixing
import Code.FK.FKMixingUpperClose

open MeasureTheory Set

namespace StatMech.FrontierB

open ConfigSpace StatMech.FK

variable {E H : Type*} [Countable E] [Group H] [MulAction H E]


def tracePullbackPatternSet (S : Finset E) (A : Set (↑S -> Bool)) :
    Set (↑S -> Nat) :=
  {a | (fun e => decide (0 < a e)) ∈ A}

theorem currentTrace_preimage_cylinder (S : Finset E)
    (A : Set (↑S -> Bool)) :
    currentTrace ⁻¹' MeasureTheory.cylinder S A =
      currentCylinder S (tracePullbackPatternSet S A) := by
  rfl

theorem currentTrace_preimage_mem_measurableCylinders
    {C : Set (ConfigSpace E)}
    (hC : C ∈ measurableCylinders (fun _ : E => Bool)) :
    currentTrace ⁻¹' C ∈ measurableCylinders (fun _ : E => Nat) := by
  rw [mem_measurableCylinders] at hC ⊢
  obtain ⟨S, A, hA, rfl⟩ := hC
  exact ⟨S, tracePullbackPatternSet S A, MeasurableSet.of_discrete,
    currentTrace_preimage_cylinder S A⟩

theorem currentTraceLaw_real (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    {A : Set (ConfigSpace E)} (hA : MeasurableSet A) :
    (currentTraceLaw mu : Measure (ConfigSpace E)).real A =
      (mu : Measure (InfiniteCurrentConfig E)).real (currentTrace ⁻¹' A) := by
  have hleft : (((currentTraceLaw mu) A : NNReal) : Real) =
      (currentTraceLaw mu : Measure (ConfigSpace E)).real A := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  have hright : ((mu (currentTrace ⁻¹' A) : NNReal) : Real) =
      (mu : Measure (InfiniteCurrentConfig E)).real (currentTrace ⁻¹' A) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft, ← hright]
  exact congrArg (fun z : NNReal => (z : Real))
    (ProbabilityMeasure.map_apply mu
      continuous_currentTrace.measurable.aemeasurable hA)

theorem currentTrace_preimage_inter_shift (g : H)
    (A B : Set (ConfigSpace E)) :
    currentTrace ⁻¹' (A ∩ (shift g) ⁻¹' B) =
      (currentTrace ⁻¹' A) ∩ (currentShift g) ⁻¹' (currentTrace ⁻¹' B) := by
  ext m
  rfl


theorem currentTraceLaw_genMixing
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (hmix : CurrentCylinderPairMixing (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    fmu_GenMixing (G := H) (currentTraceLaw mu : Measure (ConfigSpace E)) := by
  intro family hfamily epsilon hepsilon
  let pulled : Finset (Set (InfiniteCurrentConfig E)) :=
    family.image (fun A => currentTrace ⁻¹' A)
  have hpulled : ∀ A ∈ pulled,
      A ∈ measurableCylinders (fun _ : E => Nat) := by
    intro A hA
    rw [Finset.mem_image] at hA
    obtain ⟨C, hC, rfl⟩ := hA
    exact currentTrace_preimage_mem_measurableCylinders (hfamily C hC)
  obtain ⟨g, hg⟩ := hmix pulled hpulled epsilon hepsilon
  refine ⟨g, ?_⟩
  intro A hA B hB
  have hAmeas : MeasurableSet A :=
    MeasurableSet.of_mem_measurableCylinders (hfamily A hA)
  have hBmeas : MeasurableSet B :=
    MeasurableSet.of_mem_measurableCylinders (hfamily B hB)
  have hABmeas : MeasurableSet (A ∩ (shift g) ⁻¹' B) :=
    hAmeas.inter (hBmeas.preimage (measurable_shift g))
  have hPA : currentTrace ⁻¹' A ∈ pulled :=
    Finset.mem_image.mpr ⟨A, hA, rfl⟩
  have hPB : currentTrace ⁻¹' B ∈ pulled :=
    Finset.mem_image.mpr ⟨B, hB, rfl⟩
  have hcore := hg (currentTrace ⁻¹' A) hPA (currentTrace ⁻¹' B) hPB
  rw [currentTraceLaw_real mu hABmeas,
    currentTraceLaw_real mu hAmeas, currentTraceLaw_real mu hBmeas,
    currentTrace_preimage_inter_shift] 
  exact hcore


theorem infinitePlusCurrentTraceLaw_genMixing {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    fmu_GenMixing (G := Multiplicative (Lattice.Site d))
      (currentTraceLaw (infinitePlusCurrentMeasure d beta hbeta.le) :
        Measure (ConfigSpace (Sym2 (Lattice.Site d)))) :=
  currentTraceLaw_genMixing _
    (infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta)




instance sumMulAction : MulAction H (E ⊕ E) where
  smul g z := match z with
    | Sum.inl e => Sum.inl (g • e)
    | Sum.inr e => Sum.inr (g • e)
  one_smul z := by
    cases z with
    | inl e => exact congrArg Sum.inl (one_smul H e)
    | inr e => exact congrArg Sum.inr (one_smul H e)
  mul_smul g h z := by
    cases z with
    | inl e => exact congrArg Sum.inl (mul_smul g h e)
    | inr e => exact congrArg Sum.inr (mul_smul g h e)


def pairConfig (omega eta : ConfigSpace E) : ConfigSpace (E ⊕ E)
  | Sum.inl e => omega e
  | Sum.inr e => eta e

theorem measurable_pairConfig : Measurable
    (Function.uncurry pairConfig :
      ConfigSpace E × ConfigSpace E -> ConfigSpace (E ⊕ E)) := by
  rw [measurable_pi_iff]
  intro z
  cases z with
  | inl e => exact (measurable_pi_apply e).comp measurable_fst
  | inr e => exact (measurable_pi_apply e).comp measurable_snd

theorem pairConfig_shift (g : H) (omega eta : ConfigSpace E) :
    pairConfig (shift g omega) (shift g eta) =
      shift g (pairConfig omega eta) := by
  funext z
  cases z <;> rfl


noncomputable def independentPairConfigLaw
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace (E ⊕ E)) :=
  (rho.prod rho).map measurable_pairConfig.aemeasurable


def pairLeft [DecidableEq E] (T : Finset (E ⊕ E)) : Finset E :=
  T.biUnion fun z => match z with
    | Sum.inl e => {e}
    | Sum.inr _ => ∅


def pairRight [DecidableEq E] (T : Finset (E ⊕ E)) : Finset E :=
  T.biUnion fun z => match z with
    | Sum.inl _ => ∅
    | Sum.inr e => {e}

theorem pairConfig_preimage_multiOpen [DecidableEq E]
    (T : Finset (E ⊕ E)) :
    Function.uncurry pairConfig ⁻¹' fmu_multiOpen T =
      fmu_multiOpen (pairLeft T) ×ˢ fmu_multiOpen (pairRight T) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_prod, fmu_multiOpen, Set.mem_setOf_eq]
  constructor
  · intro h
    constructor
    · intro e he
      simp only [pairLeft, Finset.mem_biUnion] at he
      obtain ⟨z, hzT, hz⟩ := he
      cases z with
      | inl a =>
          have hea : e = a := by simpa using hz
          subst e
          simpa [Function.uncurry, pairConfig] using h (Sum.inl a) hzT
      | inr a => simp at hz
    · intro e he
      simp only [pairRight, Finset.mem_biUnion] at he
      obtain ⟨z, hzT, hz⟩ := he
      cases z with
      | inl a => simp at hz
      | inr a =>
          have hea : e = a := by simpa using hz
          subst e
          simpa [Function.uncurry, pairConfig] using h (Sum.inr a) hzT
  · rintro ⟨hleft, hright⟩ z hzT
    cases z with
    | inl e =>
        exact hleft e (by simp [pairLeft, hzT])
    | inr e =>
        exact hright e (by simp [pairRight, hzT])

theorem independentPairConfigLaw_real_multiOpen [DecidableEq E]
    (rho : ProbabilityMeasure (ConfigSpace E)) (T : Finset (E ⊕ E)) :
    (independentPairConfigLaw rho : Measure _).real (fmu_multiOpen T) =
      (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
        (rho : Measure _).real (fmu_multiOpen (pairRight T)) := by
  have hleft : (((independentPairConfigLaw rho) (fmu_multiOpen T) : NNReal) : Real) =
      (independentPairConfigLaw rho : Measure _).real (fmu_multiOpen T) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft]
  unfold independentPairConfigLaw
  rw [ProbabilityMeasure.map_apply _ measurable_pairConfig.aemeasurable
    (fmu_multiOpen_measurable T)]
  rw [pairConfig_preimage_multiOpen]
  rw [← measureReal_prod_prod]
  rfl

theorem pairConfig_preimage_multiOpen_inter_shift [DecidableEq E]
    (g : H) (T U : Finset (E ⊕ E)) :
    Function.uncurry pairConfig ⁻¹'
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) =
      (fmu_multiOpen (pairLeft T) ∩
          (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) ×ˢ
        (fmu_multiOpen (pairRight T) ∩
          (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
  ext p
  simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_prod]
  have hT := Set.ext_iff.mp (pairConfig_preimage_multiOpen T) p
  have hU := Set.ext_iff.mp (pairConfig_preimage_multiOpen U)
    (shift g p.1, shift g p.2)
  constructor
  · rintro ⟨hpT, hpU⟩
    have hpT' : p.1 ∈ fmu_multiOpen (pairLeft T) ∧
        p.2 ∈ fmu_multiOpen (pairRight T) := hT.mp hpT
    have hpU0 : pairConfig (shift g p.1) (shift g p.2) ∈
        fmu_multiOpen U := by rwa [pairConfig_shift]
    have hpU' : shift g p.1 ∈ fmu_multiOpen (pairLeft U) ∧
        shift g p.2 ∈ fmu_multiOpen (pairRight U) := hU.mp hpU0
    exact ⟨⟨hpT'.1, hpU'.1⟩, hpT'.2, hpU'.2⟩
  · rintro ⟨⟨hpTL, hpUL⟩, hpTR, hpUR⟩
    have hpT : pairConfig p.1 p.2 ∈ fmu_multiOpen T :=
      hT.mpr ⟨hpTL, hpTR⟩
    have hpU0 : pairConfig (shift g p.1) (shift g p.2) ∈
        fmu_multiOpen U := hU.mpr ⟨hpUL, hpUR⟩
    have hpU : shift g (pairConfig p.1 p.2) ∈ fmu_multiOpen U := by
      simpa only [pairConfig_shift] using hpU0
    exact ⟨hpT, hpU⟩

theorem independentPairConfigLaw_real_inter_shift [DecidableEq E]
    (rho : ProbabilityMeasure (ConfigSpace E)) (g : H)
    (T U : Finset (E ⊕ E)) :
    (independentPairConfigLaw rho : Measure _).real
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) =
      (rho : Measure _).real
          (fmu_multiOpen (pairLeft T) ∩
            (shift g) ⁻¹' fmu_multiOpen (pairLeft U)) *
        (rho : Measure _).real
          (fmu_multiOpen (pairRight T) ∩
            (shift g) ⁻¹' fmu_multiOpen (pairRight U)) := by
  have hset : MeasurableSet
      (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) :=
    (fmu_multiOpen_measurable T).inter
      ((fmu_multiOpen_measurable U).preimage (measurable_shift g))
  have hleft : (((independentPairConfigLaw rho)
      (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) : NNReal) : Real) =
      (independentPairConfigLaw rho : Measure _).real
        (fmu_multiOpen T ∩ (shift g) ⁻¹' fmu_multiOpen U) := by
    rw [Measure.real,
      ← ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure]
    exact (ENNReal.coe_toReal _).symm
  rw [← hleft]
  unfold independentPairConfigLaw
  rw [ProbabilityMeasure.map_apply _ measurable_pairConfig.aemeasurable hset]
  rw [pairConfig_preimage_multiOpen_inter_shift]
  rw [← measureReal_prod_prod]
  rfl


theorem independentPairConfigLaw_pairMixing
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
    fmu_PairMixing (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
  classical
  intro P epsilon hepsilon
  let Q : Finset (Finset E) :=
    P.image pairLeft ∪ P.image pairRight
  let delta := epsilon / 3
  have hdelta : 0 < delta := by dsimp [delta]; positivity
  obtain ⟨g, hg⟩ := hmix (Q.image fmu_multiOpen)
    (by
      intro A hA
      rw [Finset.mem_image] at hA
      obtain ⟨T, hT, rfl⟩ := hA
      exact fmu_multiOpen_mem_measurableCylinders T)
    delta hdelta
  refine ⟨g, ?_⟩
  intro T hT U hU
  have hTL : pairLeft T ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hTR : pairRight T ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨T, hT, rfl⟩)
  have hUL : pairLeft U ∈ Q :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hUR : pairRight U ∈ Q :=
    Finset.mem_union_right _ (Finset.mem_image.mpr ⟨U, hU, rfl⟩)
  have hleft := hg (fmu_multiOpen (pairLeft T))
    (Finset.mem_image.mpr ⟨pairLeft T, hTL, rfl⟩)
    (fmu_multiOpen (pairLeft U))
    (Finset.mem_image.mpr ⟨pairLeft U, hUL, rfl⟩)
  have hright := hg (fmu_multiOpen (pairRight T))
    (Finset.mem_image.mpr ⟨pairRight T, hTR, rfl⟩)
    (fmu_multiOpen (pairRight U))
    (Finset.mem_image.mpr ⟨pairRight U, hUR, rfl⟩)
  let a := (rho : Measure _).real
    (fmu_multiOpen (pairLeft T) ∩
      (shift g) ⁻¹' fmu_multiOpen (pairLeft U))
  let b := (rho : Measure _).real
    (fmu_multiOpen (pairRight T) ∩
      (shift g) ⁻¹' fmu_multiOpen (pairRight U))
  let c := (rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
    (rho : Measure _).real (fmu_multiOpen (pairLeft U))
  let e := (rho : Measure _).real (fmu_multiOpen (pairRight T)) *
    (rho : Measure _).real (fmu_multiOpen (pairRight U))
  have ha : 0 ≤ a := measureReal_nonneg
  have hb : 0 ≤ b := measureReal_nonneg
  have hc : 0 ≤ c := mul_nonneg measureReal_nonneg measureReal_nonneg
  have he : 0 ≤ e := mul_nonneg measureReal_nonneg measureReal_nonneg
  have hb1 : b ≤ 1 := measureReal_le_one
  have hc1 : c ≤ 1 :=
    mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
  change abs (_ - _) < epsilon
  rw [independentPairConfigLaw_real_inter_shift,
    independentPairConfigLaw_real_multiOpen,
    independentPairConfigLaw_real_multiOpen]
  change abs (a * b -
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight U)))) < epsilon
  rw [show
    ((rho : Measure _).real (fmu_multiOpen (pairLeft T)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight T))) *
    ((rho : Measure _).real (fmu_multiOpen (pairLeft U)) *
      (rho : Measure _).real (fmu_multiOpen (pairRight U))) = c * e by
      dsimp [c, e]
      ring]
  have hab : a * b - c * e = (a - c) * b + c * (b - e) := by ring
  rw [hab]
  calc
    abs ((a - c) * b + c * (b - e)) ≤
        abs (a - c) * abs b + abs c * abs (b - e) := by
      simpa [abs_mul] using abs_add_le ((a - c) * b) (c * (b - e))
    _ < delta * 1 + 1 * delta := by
      have habsB : abs b ≤ 1 := by rw [abs_of_nonneg hb]; exact hb1
      have habsC : abs c ≤ 1 := by rw [abs_of_nonneg hc]; exact hc1
      exact add_lt_add_of_lt_of_lt
        (mul_lt_mul_of_lt_of_le_of_nonneg_of_pos
          hleft habsB (abs_nonneg _) zero_lt_one)
        (mul_lt_mul_of_le_of_lt_of_nonneg_of_pos
          habsC hright (abs_nonneg _) zero_lt_one)
    _ < epsilon := by dsimp [delta]; linarith


theorem pairConfig_measurePreserving
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    MeasurePreserving (Function.uncurry pairConfig)
      (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E))
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
  change MeasurePreserving (Function.uncurry pairConfig) _
    (Measure.map (Function.uncurry pairConfig)
      ((rho : Measure (ConfigSpace E)).prod (rho : Measure (ConfigSpace E))))
  exact measurable_pairConfig.measurePreserving _

theorem independentPairConfigLaw_isTranslationInvariant
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E))) :
    IsTranslationInvariant (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) := by
  intro g
  have hprod : MeasurePreserving
      (Prod.map (shift g) (shift g))
      (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E))
      (rho.prod rho : Measure (ConfigSpace E × ConfigSpace E)) :=
    (hti g).prod (hti g)
  have hsemiconj : Function.Semiconj (Function.uncurry pairConfig)
      (Prod.map (shift g : ConfigSpace E -> ConfigSpace E)
        (shift g : ConfigSpace E -> ConfigSpace E))
      (shift g : ConfigSpace (E ⊕ E) -> ConfigSpace (E ⊕ E)) := by
    intro p
    exact pairConfig_shift g p.1 p.2
  exact (pairConfig_measurePreserving rho).of_semiconj hprod hsemiconj
    (measurable_shift g)


theorem independentPairConfigLaw_isErgodic
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
    (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
    IsErgodic (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))) :=
  fmu_isErgodic_of_pairMixing
    (independentPairConfigLaw_isTranslationInvariant rho hti)
    (independentPairConfigLaw_pairMixing rho hmix)




def pairOrConfig (omega : ConfigSpace (E ⊕ E)) : ConfigSpace E :=
  fun e => omega (Sum.inl e) || omega (Sum.inr e)

theorem measurable_pairOrConfig :
    Measurable (pairOrConfig : ConfigSpace (E ⊕ E) -> ConfigSpace E) := by
  apply Continuous.measurable
  refine continuous_pi fun e => ?_
  have hor : Continuous (fun p : Bool × Bool => p.1 || p.2) :=
    continuous_of_discreteTopology
  have hpair : Continuous (fun omega : ConfigSpace (E ⊕ E) =>
      (omega (Sum.inl e), omega (Sum.inr e))) :=
    (continuous_apply (Sum.inl e)).prodMk
      (continuous_apply (Sum.inr e))
  exact hor.comp hpair

theorem pairOrConfig_shift (g : H) : Function.Semiconj
    (pairOrConfig : ConfigSpace (E ⊕ E) -> ConfigSpace E)
    (shift g) (shift g) := by
  intro omega
  rfl


noncomputable def independentOrConfigLaw
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    ProbabilityMeasure (ConfigSpace E) :=
  (independentPairConfigLaw rho).map measurable_pairOrConfig.aemeasurable

theorem pairOrConfig_measurePreserving
    (rho : ProbabilityMeasure (ConfigSpace E)) :
    MeasurePreserving pairOrConfig
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E)))
      (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
  change MeasurePreserving pairOrConfig _
    (Measure.map pairOrConfig
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E))))
  exact measurable_pairOrConfig.measurePreserving _


theorem independentOrConfigLaw_isErgodic
    (rho : ProbabilityMeasure (ConfigSpace E))
    (herg : IsErgodic (G := H)
      (independentPairConfigLaw rho : Measure (ConfigSpace (E ⊕ E)))) :
    IsErgodic (G := H)
      (independentOrConfigLaw rho : Measure (ConfigSpace E)) := by
  refine ⟨fun g => (pairOrConfig_measurePreserving rho).of_semiconj
    (herg.1 g) (pairOrConfig_shift g) (measurable_shift g), ?_⟩
  intro s hs hinv
  have hfactor := pairOrConfig_measurePreserving rho
  have hpre : MeasurableSet (pairOrConfig ⁻¹' s) :=
    measurable_pairOrConfig hs
  have hpreInv : ∀ g : H,
      (shift g) ⁻¹' (pairOrConfig ⁻¹' s) = pairOrConfig ⁻¹' s := by
    intro g
    ext omega
    change shift g (pairOrConfig omega) ∈ s ↔ pairOrConfig omega ∈ s
    exact Set.ext_iff.mp (hinv g) (pairOrConfig omega)
  rcases herg.2 (pairOrConfig ⁻¹' s) hpre hpreInv with hzero | hfull
  · left
    rw [← hfactor.measure_preimage hs.nullMeasurableSet]
    exact hzero
  · right
    rw [← hfactor.measure_preimage hs.nullMeasurableSet,
      ← hfactor.measure_preimage MeasurableSet.univ.nullMeasurableSet]
    exact hfull

theorem independentOrConfigLaw_isErgodic_of_genMixing
    (rho : ProbabilityMeasure (ConfigSpace E))
    (hti : IsTranslationInvariant (G := H) (rho : Measure (ConfigSpace E)))
    (hmix : fmu_GenMixing (G := H) (rho : Measure (ConfigSpace E))) :
    IsErgodic (G := H)
      (independentOrConfigLaw rho : Measure (ConfigSpace E)) :=
  independentOrConfigLaw_isErgodic rho
    (independentPairConfigLaw_isErgodic rho hti hmix)


theorem independentOr_currentTraceLaw_eq_superposed
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E)) :
    (independentOrConfigLaw (currentTraceLaw mu) : Measure (ConfigSpace E)) =
      (independentSuperposedTraceLaw mu mu : Measure (ConfigSpace E)) := by
  change Measure.map pairOrConfig
      (Measure.map (Function.uncurry pairConfig)
        ((Measure.map currentTrace (mu : Measure _)).prod
          (Measure.map currentTrace (mu : Measure _)))) =
    Measure.map superposedCurrentTrace
      ((mu : Measure (InfiniteCurrentConfig E)).prod
        (mu : Measure (InfiniteCurrentConfig E)))
  rw [Measure.map_prod_map (mu : Measure (InfiniteCurrentConfig E))
    (mu : Measure (InfiniteCurrentConfig E))
    continuous_currentTrace.measurable continuous_currentTrace.measurable]
  rw [Measure.map_map measurable_pairConfig
      (continuous_currentTrace.measurable.prodMap
        continuous_currentTrace.measurable),
    Measure.map_map measurable_pairOrConfig
      (measurable_pairConfig.comp
        (continuous_currentTrace.measurable.prodMap
          continuous_currentTrace.measurable))]
  congr 1
  funext p e
  change (decide (0 < p.1 e) || decide (0 < p.2 e)) =
    decide (0 < p.1 e + p.2 e)
  simp


theorem independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing
    (mu : ProbabilityMeasure (InfiniteCurrentConfig E))
    (hti : CurrentIsTranslationInvariant (H := H)
      (mu : Measure (InfiniteCurrentConfig E)))
    (hmix : CurrentCylinderPairMixing (H := H)
      (mu : Measure (InfiniteCurrentConfig E))) :
    IsErgodic (G := H)
      (independentSuperposedTraceLaw mu mu : Measure (ConfigSpace E)) := by
  rw [← independentOr_currentTraceLaw_eq_superposed]
  exact independentOrConfigLaw_isErgodic_of_genMixing (currentTraceLaw mu)
    (hti.trace mu) (currentTraceLaw_genMixing mu hmix)


theorem plusPlusSuperposedTraceLaw_isErgodic {d : Nat}
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta) :
    IsErgodic (G := Multiplicative (Lattice.Site d))
      (independentSuperposedTraceLaw
        (infinitePlusCurrentMeasure d beta hbeta.le)
        (infinitePlusCurrentMeasure d beta hbeta.le) :
          Measure (ConfigSpace (Sym2 (Lattice.Site d)))) :=
  independentSuperposedTraceLaw_self_isErgodic_of_cylinderPairMixing _
    (infinitePlusCurrentMeasure_isTranslationInvariant d beta hbeta)
    (infinitePlusCurrentMeasure_cylinderPairMixing hd hbeta)



end StatMech.FrontierB
