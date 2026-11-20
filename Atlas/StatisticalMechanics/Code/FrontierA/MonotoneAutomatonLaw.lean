/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.MonotoneAutomatonSiteBond

open MeasureTheory
open scoped NNReal

namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


abbrev NonnegativeField (d : ℕ) := Site d → ℝ≥0



def fieldShift (g : Multiplicative (Site d)) (xi : NonnegativeField d) :
    NonnegativeField d := fun x => xi (g⁻¹ • x)

@[simp] theorem fieldShift_apply (g : Multiplicative (Site d))
    (xi : NonnegativeField d) (x : Site d) :
    fieldShift g xi x = xi (g⁻¹ • x) :=
  rfl

@[simp] theorem fieldShift_one :
    (fieldShift (1 : Multiplicative (Site d)) :
      NonnegativeField d → NonnegativeField d) = id := by
  funext xi x
  simp [fieldShift]

theorem fieldShift_mul (g h : Multiplicative (Site d)) :
    (fieldShift (g * h) : NonnegativeField d → NonnegativeField d) =
      fieldShift g ∘ fieldShift h := by
  funext xi x
  simp [fieldShift, mul_smul]

theorem measurable_fieldShift (g : Multiplicative (Site d)) :
    Measurable (fieldShift g : NonnegativeField d → NonnegativeField d) :=
  measurable_pi_lambda _ fun x => measurable_pi_apply (g⁻¹ • x)


def IsFieldTranslationInvariant (mu : Measure (NonnegativeField d)) : Prop :=
  ∀ g : Multiplicative (Site d),
    MeasurePreserving (fieldShift g : NonnegativeField d → NonnegativeField d) mu mu


def IsFieldErgodic (mu : Measure (NonnegativeField d)) : Prop :=
  IsFieldTranslationInvariant mu ∧
    ∀ s : Set (NonnegativeField d), MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (fieldShift g : NonnegativeField d → NonnegativeField d) ⁻¹' s = s) →
      mu s = 0 ∨ mu s = mu Set.univ


def raiseField (xi : NonnegativeField d) (x : Site d) (r : ℝ≥0) :
    NonnegativeField d := fun y => if y = x then max r (xi x) else xi y

@[simp] theorem raiseField_self (xi : NonnegativeField d) (x : Site d) (r : ℝ≥0) :
    raiseField xi x r x = max r (xi x) := by
  simp [raiseField]

@[simp] theorem raiseField_apply_of_ne (xi : NonnegativeField d)
    {x y : Site d} (h : y ≠ x) (r : ℝ≥0) :
    raiseField xi x r y = xi y := by
  simp [raiseField, h]


def siteCluster (eta : ConfigSpace (Site d)) (x : Site d) : Set (Site d) :=
  {y | (siteOpenGraph eta).Reachable x y}

@[simp] theorem mem_siteCluster {eta : ConfigSpace (Site d)} {x y : Site d} :
    y ∈ siteCluster eta x ↔ (siteOpenGraph eta).Reachable x y :=
  Iff.rfl





structure MonotoneAutomaton (d : ℕ) where
  toFun : NonnegativeField d → ConfigSpace (Site d)
  measurable_toFun : Measurable toFun
  equivariant : ∀ (g : Multiplicative (Site d)) (xi : NonnegativeField d),
    toFun (fieldShift g xi) = shift g (toFun xi)
  monotone : Monotone toFun
  threshold : ℝ≥0
  occupationThreshold : ∀ (xi : NonnegativeField d) (x : Site d),
    threshold ≤ xi x → toFun xi x = true
  otherInfiniteClustersStable : ∀ (xi : NonnegativeField d) (x : Site d)
    (r : ℝ≥0) (y : Site d),
    y ∉ siteCluster (toFun (raiseField xi x r)) x →
    (siteCluster (toFun (raiseField xi x r)) y).Infinite →
    (siteCluster (toFun xi) y).Infinite

instance : CoeFun (MonotoneAutomaton d)
    (fun _ => NonnegativeField d → ConfigSpace (Site d)) :=
  ⟨MonotoneAutomaton.toFun⟩


noncomputable def automatonSiteLaw (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) : Measure (ConfigSpace (Site d)) :=
  Measure.map T mu


noncomputable def automatonBondLaw (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) :
    Measure (ConfigSpace (Sym2 (Site d))) :=
  Measure.map (siteToBond ∘ T) mu



theorem automatonBondLaw_eq_map_siteToBond (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) :
    automatonBondLaw T mu = Measure.map siteToBond (automatonSiteLaw T mu) := by
  unfold automatonBondLaw automatonSiteLaw
  rw [Measure.map_map measurable_siteToBond T.measurable_toFun]



theorem automatonSiteLaw_isTranslationInvariant (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d))
    (hinv : IsFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (automatonSiteLaw T mu) := by
  intro g
  refine ⟨measurable_shift g, ?_⟩
  unfold automatonSiteLaw
  rw [Measure.map_map (measurable_shift g) T.measurable_toFun]
  have hcomp :
      (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ∘ T =
        T ∘ (fieldShift g : NonnegativeField d → NonnegativeField d) := by
    funext xi
    exact (T.equivariant g xi).symm
  rw [hcomp, ← Measure.map_map T.measurable_toFun (measurable_fieldShift g),
    (hinv g).map_eq]



theorem automatonSiteLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) (herg : IsFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (automatonSiteLaw T mu) := by
  refine ⟨automatonSiteLaw_isTranslationInvariant T mu herg.1, ?_⟩
  intro s hs hinv
  have hpreMeas : MeasurableSet (T ⁻¹' s) := T.measurable_toFun hs
  have hpreInv : ∀ g : Multiplicative (Site d),
      (fieldShift g : NonnegativeField d → NonnegativeField d) ⁻¹' (T ⁻¹' s) =
        T ⁻¹' s := by
    intro g
    ext xi
    simp only [Set.mem_preimage]
    rw [T.equivariant, ← Set.mem_preimage, hinv g]
  rcases herg.2 _ hpreMeas hpreInv with hzero | hfull
  · left
    rwa [automatonSiteLaw, Measure.map_apply T.measurable_toFun hs]
  · right
    rw [automatonSiteLaw, Measure.map_apply T.measurable_toFun hs, hfull,
      Measure.map_apply T.measurable_toFun MeasurableSet.univ]
    rfl


theorem automatonBondLaw_isTranslationInvariant (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d))
    (hinv : IsFieldTranslationInvariant mu) :
    IsTranslationInvariant (G := Multiplicative (Site d))
      (automatonBondLaw T mu) := by
  rw [automatonBondLaw_eq_map_siteToBond]
  exact siteToBond_isTranslationInvariant _
    (automatonSiteLaw_isTranslationInvariant T mu hinv)


theorem automatonBondLaw_isErgodic (T : MonotoneAutomaton d)
    (mu : Measure (NonnegativeField d)) (herg : IsFieldErgodic mu) :
    IsErgodic (G := Multiplicative (Site d)) (automatonBondLaw T mu) := by
  rw [automatonBondLaw_eq_map_siteToBond]
  exact siteToBond_isErgodic _ (automatonSiteLaw_isErgodic T mu herg)

end StatMech.FrontierA
