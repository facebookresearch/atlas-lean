/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Translate covering of convex bodies

Source: Arman, Bondarenko and Prymak, arXiv:2404.00547v1, introduction.
The abstract defines the Hadwiger numbers universally over bodies; the displayed
minimum over bodies in the introduction is inconsistent with that definition.
-/

@[expose] public section

namespace ConvexCovering

/-- A convex body is compact and convex with nonempty ambient interior. -/
def IsConvexBody {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  IsCompact K ∧ Convex ℝ K ∧ (interior K).Nonempty

/-- A `q`-indexed family of actual translates of `L` covers `K`. -/
def CoveredByTranslates {n : ℕ} (K L : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : Prop :=
  ∃ translations : Fin q → EuclideanSpace ℝ (Fin n),
    K ⊆ ⋃ i, (fun x ↦ translations i + x) '' L

/-- An actual interior-translate cover of a body. -/
def CoveredByInteriorTranslates {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n)))
    (q : ℕ) : Prop :=
  CoveredByTranslates K (interior K) q

/-- One bound for every `n`-dimensional convex body, not a minimum over bodies. -/
def UniformInteriorTranslateBound (n q : ℕ) : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsConvexBody K → CoveredByInteriorTranslates K q

/-- Central symmetry about an actual center. -/
def IsCentrallySymmetric {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∃ c : EuclideanSpace ℝ (Fin n),
    ∀ x, x ∈ K ↔ c + c - x ∈ K

/-- The uniform bound restricted to centrally symmetric convex bodies. -/
def UniformSymmetricInteriorTranslateBound (n q : ℕ) : Prop :=
  ∀ K : Set (EuclideanSpace ℝ (Fin n)),
    IsConvexBody K → IsCentrallySymmetric K → CoveredByInteriorTranslates K q

/-- A finite cover by smaller positive homothets, with repetitions allowed. -/
def CoveredBySmallerPositiveHomothets {n : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) (q : ℕ) : Prop :=
  ∃ (r : Fin q → ℝ) (v : Fin q → EuclideanSpace ℝ (Fin n)),
    (∀ i, 0 < r i ∧ r i < 1) ∧
      ∀ x ∈ K, ∃ i, x ∈ (fun y ↦ v i + r i • y) '' K

/-- The actual minimum translate count, with infinity when no finite cover exists. -/
noncomputable def translateCoveringNumber {n : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n))) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q : ℕ | CoveredByTranslates K L q})

/-- The least universal interior-cover bound, or infinity if no finite bound exists. -/
noncomputable def hadwigerCoveringNumber (n : ℕ) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) '' {q : ℕ | UniformInteriorTranslateBound n q})

/-- The least universal bound over centrally symmetric bodies, or infinity. -/
noncomputable def symmetricHadwigerCoveringNumber (n : ℕ) : WithTop ℕ :=
  sInf ((fun q : ℕ ↦ (q : WithTop ℕ)) ''
    {q : ℕ | UniformSymmetricInteriorTranslateBound n q})

/-- Membership in a translate cover, without unfolding indexed unions. -/
theorem coveredByTranslates_iff {n q : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n))) :
    CoveredByTranslates K L q ↔
      ∃ v : Fin q → EuclideanSpace ℝ (Fin n), ∀ x ∈ K, ∃ i, x ∈ (fun y ↦ v i + y) '' L := by
  constructor
  · rintro ⟨v, h⟩
    exact ⟨v, fun x hx ↦ Set.mem_iUnion.mp (h hx)⟩
  · rintro ⟨v, h⟩
    exact ⟨v, fun x hx ↦ Set.mem_iUnion.mpr (h x hx)⟩

/-- Interior covering is the generic translate cover specialized to the actual interior. -/
theorem coveredByInteriorTranslates_iff {n q : ℕ}
    (K : Set (EuclideanSpace ℝ (Fin n))) :
    CoveredByInteriorTranslates K q ↔ CoveredByTranslates K (interior K) q :=
  Iff.rfl

private theorem castCount_sInf_eq_of_isLeast (P : ℕ → Prop) (q : ℕ)
    (h : IsLeast {r : ℕ | P r} q) :
    sInf ((fun r : ℕ ↦ (r : WithTop ℕ)) '' {r : ℕ | P r}) = (q : WithTop ℕ) := by
  apply IsLeast.csInf_eq
  refine ⟨⟨q, h.1, rfl⟩, ?_⟩
  rintro _ ⟨r, hr, rfl⟩
  exact WithTop.coe_le_coe.mpr (h.2 hr)

/-- A witnessed least finite translate count gives the actual extended-natural value. -/
theorem translateCoveringNumber_eq_of_isLeast {n q : ℕ}
    (K L : Set (EuclideanSpace ℝ (Fin n)))
    (h : IsLeast {r : ℕ | CoveredByTranslates K L r} q) :
    translateCoveringNumber K L = (q : WithTop ℕ) :=
  castCount_sInf_eq_of_isLeast _ q h

/-- A least universal count gives the Hadwiger number without any finiteness oracle. -/
theorem hadwigerCoveringNumber_eq_of_isLeast {n q : ℕ}
    (h : IsLeast {r : ℕ | UniformInteriorTranslateBound n r} q) :
    hadwigerCoveringNumber n = (q : WithTop ℕ) :=
  castCount_sInf_eq_of_isLeast _ q h

/-- The same characteristic API for the centrally symmetric class. -/
theorem symmetricHadwigerCoveringNumber_eq_of_isLeast {n q : ℕ}
    (h : IsLeast {r : ℕ | UniformSymmetricInteriorTranslateBound n r} q) :
    symmetricHadwigerCoveringNumber n = (q : WithTop ℕ) :=
  castCount_sInf_eq_of_isLeast _ q h

end ConvexCovering
