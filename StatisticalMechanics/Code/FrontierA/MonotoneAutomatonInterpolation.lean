/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierA.MonotoneAutomatonLaw

open MeasureTheory

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


abbrev FieldTriple (d : ℕ) :=
  NonnegativeField d × (NonnegativeField d × NonnegativeField d)


def tripleFieldShift (g : Multiplicative (Site d)) (q : FieldTriple d) :
    FieldTriple d :=
  (fieldShift g q.1, fieldShift g q.2.1, fieldShift g q.2.2)

@[simp] theorem tripleFieldShift_fst (g : Multiplicative (Site d))
    (q : FieldTriple d) : (tripleFieldShift g q).1 = fieldShift g q.1 :=
  rfl

@[simp] theorem tripleFieldShift_snd_fst (g : Multiplicative (Site d))
    (q : FieldTriple d) : (tripleFieldShift g q).2.1 = fieldShift g q.2.1 :=
  rfl

@[simp] theorem tripleFieldShift_snd_snd (g : Multiplicative (Site d))
    (q : FieldTriple d) : (tripleFieldShift g q).2.2 = fieldShift g q.2.2 :=
  rfl

@[simp] theorem tripleFieldShift_one :
    (tripleFieldShift (1 : Multiplicative (Site d)) :
      FieldTriple d → FieldTriple d) = id := by
  funext q
  rcases q with ⟨low, middle, high⟩
  simp [tripleFieldShift]

theorem tripleFieldShift_mul (g h : Multiplicative (Site d)) :
    (tripleFieldShift (g * h) : FieldTriple d → FieldTriple d) =
      tripleFieldShift g ∘ tripleFieldShift h := by
  funext q
  rcases q with ⟨low, middle, high⟩
  simp [tripleFieldShift, fieldShift_mul]

theorem measurable_tripleFieldShift (g : Multiplicative (Site d)) :
    Measurable (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
  exact (measurable_fieldShift g).comp measurable_fst |>.prodMk
    (((measurable_fieldShift g).comp measurable_snd.fst).prodMk
      ((measurable_fieldShift g).comp measurable_snd.snd))


def IsTripleFieldTranslationInvariant (mu : Measure (FieldTriple d)) : Prop :=
  ∀ g : Multiplicative (Site d),
    MeasurePreserving (tripleFieldShift g : FieldTriple d → FieldTriple d) mu mu


def IsTripleFieldErgodic (mu : Measure (FieldTriple d)) : Prop :=
  IsTripleFieldTranslationInvariant mu ∧
    ∀ s : Set (FieldTriple d), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (tripleFieldShift g : FieldTriple d → FieldTriple d) ⁻¹' s = s) →
      mu s = 0 ∨ mu s = mu Set.univ


def IsMonotoneFieldTriple (q : FieldTriple d) : Prop :=
  q.1 ≤ q.2.1 ∧ q.2.1 ≤ q.2.2



noncomputable def interpolatedSite (T : MonotoneAutomaton d) (q : FieldTriple d) :
    ConfigSpace (Site d) := fun x =>
  T q.1 x || decide (T.threshold ≤ q.2.1 x)

@[simp] theorem interpolatedSite_apply (T : MonotoneAutomaton d)
    (q : FieldTriple d) (x : Site d) :
    interpolatedSite T q x =
      (T q.1 x || decide (T.threshold ≤ q.2.1 x)) :=
  rfl


theorem measurable_interpolatedSite (T : MonotoneAutomaton d) :
    Measurable (interpolatedSite T : FieldTriple d → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  intro x
  change Measurable (fun q : FieldTriple d =>
    T q.1 x || decide (T.threshold ≤ q.2.1 x))
  have hT : Measurable (fun q : FieldTriple d => T q.1 x) :=
    measurable_pi_iff.mp (T.measurable_toFun.comp measurable_fst) x
  have hcoord : Measurable (fun q : FieldTriple d => q.2.1 x) :=
    (measurable_pi_apply x).comp measurable_snd.fst
  have hthreshold : Measurable (fun q : FieldTriple d =>
      decide (T.threshold ≤ q.2.1 x)) := by
    apply measurable_to_bool
    convert hcoord (measurableSet_Ici : MeasurableSet (Set.Ici T.threshold)) using 1
    ext q
    simp
  have hor : Measurable (fun p : Bool × Bool => p.1 || p.2) :=
    Measurable.of_discrete
  exact hor.comp (hT.prodMk hthreshold)


theorem interpolatedSite_shift (T : MonotoneAutomaton d)
    (g : Multiplicative (Site d)) (q : FieldTriple d) :
    interpolatedSite T (tripleFieldShift g q) =
      shift g (interpolatedSite T q) := by
  funext x
  simp only [interpolatedSite, tripleFieldShift_fst,
    tripleFieldShift_snd_fst, T.equivariant, shift_apply, fieldShift_apply]
  rfl


theorem automatonLow_le_interpolated (T : MonotoneAutomaton d)
    (q : FieldTriple d) : T q.1 ≤ interpolatedSite T q := by
  intro x
  cases h : T q.1 x <;> simp [interpolatedSite, h]



theorem interpolated_le_automatonMiddle (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    interpolatedSite T q ≤ T q.2.1 := by
  have hmono : T q.1 ≤ T q.2.1 := T.monotone hq.1
  intro x
  by_cases ht : T.threshold ≤ q.2.1 x
  · have hopen : T q.2.1 x = true := T.occupationThreshold q.2.1 x ht
    simp [hopen]
  · simpa [interpolatedSite, ht] using hmono x


theorem automatonMiddle_le_automatonHigh (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    T q.2.1 ≤ T q.2.2 :=
  T.monotone hq.2


theorem monotoneAutomaton_interpolation_sandwich (T : MonotoneAutomaton d)
    (q : FieldTriple d) (hq : IsMonotoneFieldTriple q) :
    T q.1 ≤ interpolatedSite T q ∧
      interpolatedSite T q ≤ T q.2.1 ∧ T q.2.1 ≤ T q.2.2 :=
  ⟨automatonLow_le_interpolated T q,
    interpolated_le_automatonMiddle T q hq,
    automatonMiddle_le_automatonHigh T q hq⟩


noncomputable def interpolatedSiteLaw (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) : Measure (ConfigSpace (Site d)) :=
  Measure.map (interpolatedSite T) mu


noncomputable def interpolatedBondLaw (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) :
    Measure (ConfigSpace (Sym2 (Site d))) :=
  Measure.map (siteToBond ∘ interpolatedSite T) mu

theorem interpolatedBondLaw_eq_map_siteToBond (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) :
    interpolatedBondLaw T mu =
      Measure.map siteToBond (interpolatedSiteLaw T mu) := by
  unfold interpolatedBondLaw interpolatedSiteLaw
  rw [Measure.map_map measurable_siteToBond (measurable_interpolatedSite T)]


theorem interpolatedSiteLaw_isTranslationInvariant (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d))
    (hinv : IsTripleFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (interpolatedSiteLaw T mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  unfold interpolatedSiteLaw
  rw [Measure.map_map (measurable_shift g) (measurable_interpolatedSite T)]
  have hcomp :
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ∘ interpolatedSite T =
        interpolatedSite T ∘ (tripleFieldShift g : FieldTriple d → FieldTriple d) := by
    funext q
    exact (interpolatedSite_shift T g q).symm
  rw [hcomp,
    ← Measure.map_map (measurable_interpolatedSite T) (measurable_tripleFieldShift g),
    (hinv g).map_eq]


theorem interpolatedSiteLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) (herg : IsTripleFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (interpolatedSiteLaw T mu) := by
  refine ⟨interpolatedSiteLaw_isTranslationInvariant T mu herg.1, ?_⟩
  intro s hs hinv
  have hpreMeas : MeasurableSet ((interpolatedSite T) ⁻¹' s) :=
    measurable_interpolatedSite T hs
  have hpreInv : ∀ g : Multiplicative (Site d),
      (tripleFieldShift g : FieldTriple d → FieldTriple d) ⁻¹'
          ((interpolatedSite T) ⁻¹' s) = (interpolatedSite T) ⁻¹' s := by
    intro g
    ext q
    simp only [Set.mem_preimage]
    rw [interpolatedSite_shift, ← Set.mem_preimage, hinv g]
  rcases herg.2 _ hpreMeas hpreInv with hzero | hfull
  · left
    rwa [interpolatedSiteLaw,
      Measure.map_apply (measurable_interpolatedSite T) hs]
  · right
    rw [interpolatedSiteLaw,
      Measure.map_apply (measurable_interpolatedSite T) hs, hfull,
      Measure.map_apply (measurable_interpolatedSite T) MeasurableSet.univ]
    rfl



theorem interpolatedBondLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (FieldTriple d)) (herg : IsTripleFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (interpolatedBondLaw T mu) := by
  rw [interpolatedBondLaw_eq_map_siteToBond]
  exact siteToBond_isErgodic _ (interpolatedSiteLaw_isErgodic T mu herg)

end StatMech.FrontierA
