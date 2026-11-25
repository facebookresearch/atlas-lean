/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
public import Mathlib.Algebra.Category.ModuleCat.Ext.DimensionShifting
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Projective dimension under exact module functors

An additive functor between the original module categories that preserves
finite limits, finite colimits, and projective objects carries an actual
projective-dimension bound to the same bound. The proof uses the original
projective short complex of the source module, maps its actual short exact
row, and inducts on the dimension of its original kernel.

The rings and both module-carrier universes are independent. Only the source
ring is required to be small in its module universe, for its original
projective cover. No Noetherian or commutativity hypothesis is used.

For an additive equivalence, projective preservation is derived from the
actual equivalence adjunction. Applying the bound theorem in both directions
gives invariance of the existing projective-dimension predicate and of the
original `WithBot ℕ∞` projective dimension, including zero objects and
infinite dimension. No resolution or dimension outcome is a hypothesis.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe vR vS uR uS

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

section ExactFunctor

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S] [Small.{vR} R]
variable (F : ModuleCat.{vR} R ⥤ ModuleCat.{vS} S) [F.Additive]
variable [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- An exact additive functor preserving projectives carries every
actual projective-dimension bound to the same bound. The successor proof
uses the mapped original projective cover and its original kernel. -/
theorem hasProjectiveDimensionLE_map
    (hF : ∀ P : ModuleCat.{vR} R, Projective P → Projective (F.obj P))
    (M : ModuleCat.{vR} R) (n : ℕ) (hM : HasProjectiveDimensionLE M n) :
    HasProjectiveDimensionLE (F.obj M) n := by
  induction n generalizing M with
  | zero =>
      have hP : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr hM
      exact (projective_iff_hasProjectiveDimensionLE_zero (F.obj M)).mp (hF M hP)
  | succ n ih =>
      let T := M.projectiveShortComplex
      have hT : T.ShortExact := M.shortExact_projectiveShortComplex
      have hKernel : HasProjectiveDimensionLE T.X₁ n :=
        (hT.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp hM
      have hMappedKernel : HasProjectiveDimensionLE (F.obj T.X₁) n :=
        ih T.X₁ hKernel
      have hMappedRow : (T.map F).ShortExact := hT.map_of_exact F
      have hMappedProjective : Projective (T.map F).X₂ := hF T.X₂ inferInstance
      exact (hMappedRow.hasProjectiveDimensionLT_X₃_iff n hMappedProjective).mpr hMappedKernel

/-- Strict projective-dimension bounds are preserved as well, including
the bound zero, which says that the actual object is zero. -/
theorem hasProjectiveDimensionLT_map
    (hF : ∀ P : ModuleCat.{vR} R, Projective P → Projective (F.obj P))
    (M : ModuleCat.{vR} R) (n : ℕ) (hM : HasProjectiveDimensionLT M n) :
    HasProjectiveDimensionLT (F.obj M) n := by
  cases n with
  | zero =>
      letI : HasProjectiveDimensionLT M 0 := hM
      exact (F.map_isZero (isZero_of_hasProjectiveDimensionLT_zero M)).hasProjectiveDimensionLT_zero
  | succ n =>
      exact hasProjectiveDimensionLE_map F hF M n hM

end ExactFunctor

section AdditiveEquivalence

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]
variable [Small.{vR} R] [Small.{vS} S]
variable (E : ModuleCat.{vR} R ≌ ModuleCat.{vS} S)
variable [E.functor.Additive] [E.inverse.Additive]

/-- Actual additive module equivalences preserve and reflect strict
projective-dimension bounds. Reflection uses the literal inverse and
the original equivalence unit on the source module. -/
theorem hasProjectiveDimensionLT_equivalence_iff (M : ModuleCat.{vR} R) (n : ℕ) :
    HasProjectiveDimensionLT (E.functor.obj M) n ↔ HasProjectiveDimensionLT M n := by
  constructor
  · intro hM
    have hInverse : HasProjectiveDimensionLT (E.inverse.obj (E.functor.obj M)) n :=
      hasProjectiveDimensionLT_map E.inverse
        (fun P hP => (E.symm.map_projective_iff P).mpr hP) (E.functor.obj M) n hM
    letI : HasProjectiveDimensionLT ((E.functor ⋙ E.inverse).obj M) n := hInverse
    exact hasProjectiveDimensionLT_of_iso (E.unitIso.app M).symm n
  · intro hM
    exact hasProjectiveDimensionLT_map E.functor
      (fun P hP => (E.map_projective_iff P).mpr hP) M n hM

/-- The same exact additive equivalence preserves and reflects each
original non-strict projective-dimension bound. -/
theorem hasProjectiveDimensionLE_equivalence_iff (M : ModuleCat.{vR} R) (n : ℕ) :
    HasProjectiveDimensionLE (E.functor.obj M) n ↔ HasProjectiveDimensionLE M n :=
  hasProjectiveDimensionLT_equivalence_iff E M (n + 1)

/-- The original numeric projective dimension is invariant under actual
additive module equivalences, retaining its bottom and infinite values. -/
theorem projectiveDimension_equivalence (M : ModuleCat.{vR} R) :
    projectiveDimension (E.functor.obj M) = projectiveDimension M := by
  simp only [projectiveDimension]
  congr! 5
  exact hasProjectiveDimensionLT_equivalence_iff E M _

end AdditiveEquivalence

end ModuleCat

end
