/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/












import Code.FrontierA.MonotoneAutomatonInterpolation

open MeasureTheory
open scoped ENNReal NNReal

namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


def SiteEventIgnores (x : Site d) (B : Set (ConfigSpace (Site d))) : Prop :=
  ∀ eta eta' : ConfigSpace (Site d),
    (∀ y, y ≠ x → eta y = eta' y) → (eta ∈ B ↔ eta' ∈ B)



def TripleEventIgnoresMiddleAt (x : Site d) (A : Set (FieldTriple d)) : Prop :=
  ∀ q q' : FieldTriple d,
    q.1 = q'.1 →
    (∀ y, y ≠ x → q.2.1 y = q'.2.1 y) →
    (q ∈ A ↔ q' ∈ A)



def HasMiddleInsertionLowerBound (mu : Measure (FieldTriple d))
    (t : ℝ≥0) (epsilon : ℝ≥0∞) : Prop :=
  ∀ (x : Site d) (A : Set (FieldTriple d)), MeasurableSet A →
    TripleEventIgnoresMiddleAt x A →
    epsilon * mu A ≤ mu (A ∩ {q | t ≤ q.2.1 x})


def HasSiteInsertionLowerBound (nu : Measure (ConfigSpace (Site d)))
    (epsilon : ℝ≥0∞) : Prop :=
  ∀ (x : Site d) (B : Set (ConfigSpace (Site d))), MeasurableSet B →
    SiteEventIgnores x B →
    epsilon * nu B ≤ nu (B ∩ {eta | eta x = true})



theorem tripleEventIgnoresMiddleAt_preimage_interpolatedSite
    (T : MonotoneAutomaton d) (x : Site d)
    (B : Set (ConfigSpace (Site d))) (hB : SiteEventIgnores x B) :
    TripleEventIgnoresMiddleAt x ((interpolatedSite T) ⁻¹' B) := by
  intro q q' hlow hmiddle
  apply hB
  intro y hy
  simp only [interpolatedSite_apply]
  rw [hlow, hmiddle y hy]


theorem measurableSet_middleThreshold (t : ℝ≥0) (x : Site d) :
    MeasurableSet {q : FieldTriple d | t ≤ q.2.1 x} := by
  have hcoord : Measurable (fun q : FieldTriple d => q.2.1 x) :=
    (measurable_pi_apply x).comp measurable_snd.fst
  exact hcoord measurableSet_Ici



theorem interpolatedSite_eq_true_of_middleThreshold
    (T : MonotoneAutomaton d) (q : FieldTriple d) (x : Site d)
    (h : T.threshold ≤ q.2.1 x) : interpolatedSite T q x = true := by
  simp [interpolatedSite, h]


theorem interpolatedSiteLaw_hasInsertionLowerBound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    (epsilon : ℝ≥0∞)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
    HasSiteInsertionLowerBound (interpolatedSiteLaw T mu) epsilon := by
  intro x B hBmeas hBoff
  let A : Set (FieldTriple d) := (interpolatedSite T) ⁻¹' B
  have hAmeas : MeasurableSet A := measurable_interpolatedSite T hBmeas
  have hAoff : TripleEventIgnoresMiddleAt x A :=
    tripleEventIgnoresMiddleAt_preimage_interpolatedSite T x B hBoff
  have hR3 := hinsert x A hAmeas hAoff
  have hsub : A ∩ {q : FieldTriple d | T.threshold ≤ q.2.1 x} ⊆
      (interpolatedSite T) ⁻¹' (B ∩ {eta | eta x = true}) := by
    rintro q ⟨hqA, hqt⟩
    exact ⟨hqA, interpolatedSite_eq_true_of_middleThreshold T q x hqt⟩
  have htargetMeas : MeasurableSet (B ∩ {eta | eta x = true}) := by
    apply hBmeas.inter
    exact measurableSet_eq_fun (measurable_pi_apply x) measurable_const
  calc
    epsilon * interpolatedSiteLaw T mu B = epsilon * mu A := by
      rw [interpolatedSiteLaw,
        Measure.map_apply (measurable_interpolatedSite T) hBmeas]
    _ ≤ mu (A ∩ {q : FieldTriple d | T.threshold ≤ q.2.1 x}) := hR3
    _ ≤ mu ((interpolatedSite T) ⁻¹' (B ∩ {eta | eta x = true})) :=
      measure_mono hsub
    _ = interpolatedSiteLaw T mu (B ∩ {eta | eta x = true}) := by
      rw [interpolatedSiteLaw,
        Measure.map_apply (measurable_interpolatedSite T) htargetMeas]



theorem siteInsertion_positive
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ℝ≥0∞)
    (hepsilon : 0 < epsilon) (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (x : Site d) (B : Set (ConfigSpace (Site d))) (hBmeas : MeasurableSet B)
    (hBoff : SiteEventIgnores x B) (hBpos : 0 < nu B) :
    0 < nu (B ∩ {eta | eta x = true}) := by
  have hle := hinsert x B hBmeas hBoff
  exact lt_of_lt_of_le (ENNReal.mul_pos hepsilon.ne' hBpos.ne') hle




def forceSiteOccupied (x : Site d) (eta : ConfigSpace (Site d)) :
    ConfigSpace (Site d) := fun y => if y = x then true else eta y

@[simp] theorem forceSiteOccupied_self (x : Site d)
    (eta : ConfigSpace (Site d)) : forceSiteOccupied x eta x = true := by
  simp [forceSiteOccupied]

@[simp] theorem forceSiteOccupied_apply_of_ne {x y : Site d} (h : y ≠ x)
    (eta : ConfigSpace (Site d)) : forceSiteOccupied x eta y = eta y := by
  simp [forceSiteOccupied, h]

theorem measurable_forceSiteOccupied (x : Site d) :
    Measurable (forceSiteOccupied x :
      ConfigSpace (Site d) → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  intro y
  by_cases h : y = x
  · subst y
    simp [forceSiteOccupied]
  · simpa [forceSiteOccupied, h] using (measurable_pi_apply y)


theorem forceSiteOccupied_eq_self_of_eq_true (x : Site d)
    (eta : ConfigSpace (Site d)) (h : eta x = true) :
    forceSiteOccupied x eta = eta := by
  funext y
  by_cases hy : y = x
  · subst y
    simp [h]
  · simp [forceSiteOccupied, hy]


theorem siteEventIgnores_forceSiteOccupied_preimage (x : Site d)
    (B : Set (ConfigSpace (Site d))) :
    SiteEventIgnores x ((forceSiteOccupied x) ⁻¹' B) := by
  intro eta eta' hagree
  have heq : forceSiteOccupied x eta = forceSiteOccupied x eta' := by
    funext y
    by_cases hy : y = x
    · subst y
      simp
    · simp [forceSiteOccupied, hy, hagree y hy]
  rw [Set.mem_preimage, Set.mem_preimage, heq]



theorem forceSiteOccupied_map_absolutelyContinuous
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) (x : Site d) :
    nu.map (forceSiteOccupied x) ≪ nu := by
  apply Measure.AbsolutelyContinuous.mk
  intro B hBmeas hBzero
  rw [Measure.map_apply (measurable_forceSiteOccupied x) hBmeas]
  let A : Set (ConfigSpace (Site d)) := (forceSiteOccupied x) ⁻¹' B
  have hAmeas : MeasurableSet A := measurable_forceSiteOccupied x hBmeas
  have hAoff : SiteEventIgnores x A :=
    siteEventIgnores_forceSiteOccupied_preimage x B
  have hle := hinsert x A hAmeas hAoff
  have hsub : A ∩ {eta : ConfigSpace (Site d) | eta x = true} ⊆ B := by
    rintro eta ⟨hetaB, hetaOpen⟩
    have hfix := forceSiteOccupied_eq_self_of_eq_true x eta hetaOpen
    simpa only [A, Set.mem_preimage, hfix] using hetaB
  have hinterZero : nu (A ∩ {eta : ConfigSpace (Site d) | eta x = true}) = 0 :=
    measure_mono_null hsub hBzero
  rw [hinterZero] at hle
  have hmul : epsilon * nu A = 0 := nonpos_iff_eq_zero.mp hle
  exact (mul_eq_zero.mp hmul).resolve_left hepsilon


def forceSitesOccupied (S : Finset (Site d)) (eta : ConfigSpace (Site d)) :
    ConfigSpace (Site d) := fun y => if y ∈ S then true else eta y

@[simp] theorem forceSitesOccupied_apply (S : Finset (Site d))
    (eta : ConfigSpace (Site d)) (y : Site d) :
    forceSitesOccupied S eta y = if y ∈ S then true else eta y :=
  rfl

@[simp] theorem forceSitesOccupied_empty (eta : ConfigSpace (Site d)) :
    forceSitesOccupied (∅ : Finset (Site d)) eta = eta := by
  funext y
  simp [forceSitesOccupied]

theorem forceSitesOccupied_insert (x : Site d) (S : Finset (Site d)) :
    (forceSitesOccupied (insert x S) :
      ConfigSpace (Site d) → ConfigSpace (Site d)) =
      forceSiteOccupied x ∘ forceSitesOccupied S := by
  funext eta y
  by_cases hyx : y = x
  · subst y
    simp [forceSitesOccupied, forceSiteOccupied]
  · simp [forceSitesOccupied, forceSiteOccupied, hyx]

theorem measurable_forceSitesOccupied (S : Finset (Site d)) :
    Measurable (forceSitesOccupied S :
      ConfigSpace (Site d) → ConfigSpace (Site d)) := by
  rw [measurable_pi_iff]
  intro y
  by_cases h : y ∈ S
  · simp [forceSitesOccupied, h]
  · simpa [forceSitesOccupied, h] using (measurable_pi_apply y)



theorem forceSitesOccupied_map_absolutelyContinuous
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) (S : Finset (Site d)) :
    nu.map (forceSitesOccupied S) ≪ nu := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      rw [show (forceSitesOccupied (∅ : Finset (Site d)) :
        ConfigSpace (Site d) → ConfigSpace (Site d)) = id by
          funext eta
          exact forceSitesOccupied_empty eta]
      simpa using Measure.absolutelyContinuous_refl nu
  | @insert x S hx ih =>
      rw [forceSitesOccupied_insert,
        ← Measure.map_map (measurable_forceSiteOccupied x)
          (measurable_forceSitesOccupied S)]
      exact (ih.map (measurable_forceSiteOccupied x)).trans
        (forceSiteOccupied_map_absolutelyContinuous nu epsilon hepsilon hinsert x)



theorem positive_of_forceSitesOccupied_preimage
    (nu : Measure (ConfigSpace (Site d))) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (S : Finset (Site d))
    {A B : Set (ConfigSpace (Site d))} (hBmeas : MeasurableSet B)
    (hsub : A ⊆ (forceSitesOccupied S) ⁻¹' B) (hApos : 0 < nu A) :
    0 < nu B := by
  by_contra hBpos
  rw [not_lt, nonpos_iff_eq_zero] at hBpos
  have hac := forceSitesOccupied_map_absolutelyContinuous
    nu epsilon hepsilon hinsert S
  have hmapZero : nu.map (forceSitesOccupied S) B = 0 := hac hBpos
  have hpreZero : nu ((forceSitesOccupied S) ⁻¹' B) = 0 := by
    rw [← Measure.map_apply (measurable_forceSitesOccupied S) hBmeas]
    exact hmapZero
  have hAle : nu A ≤ nu ((forceSitesOccupied S) ⁻¹' B) := measure_mono hsub
  rw [hpreZero] at hAle
  exact (not_lt_of_ge hAle) hApos

end StatMech.FrontierA
