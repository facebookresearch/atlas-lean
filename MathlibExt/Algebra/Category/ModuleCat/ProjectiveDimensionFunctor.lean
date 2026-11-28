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
# Projective-dimension transport through exact module functors

Let R,S be rings with independent scalar and module universes. Assume R can be represented in
its module universe vR. An additive functor F:R-Mod_{vR}→S-Mod_{vS} preserving finite limits,
finite colimits and projective objects carries pd(M)≤n to pd(FM)≤n. It also carries strict
bounds, including pd(M)<0, which denotes the zero object.

For an equivalence of module categories, assume each ring is representable in its respective
module universe and both the forward and inverse functors are additive. Exactness and projective
preservation follow from the equivalence. Applying the transport in both directions identifies
each strict and non-strict dimension bound and gives pd(E(M))=pd(M) in ℕ∞ with its extra bottom
value for zero objects. No commutativity assumption on the rings is required.
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

/-- Let R,S be rings in independent universes uR,uS, with module universes vR,vS. Assume R can be
represented in vR, and F:R-Mod_{vR}→S-Mod_{vS} is additive, preserves finite limits and finite
colimits, and sends projective objects to projective objects. For M in R-Mod_{vR}, n∈ℕ and
pd(M)≤n, one has pd(FM)≤n. The finite-limit and finite-colimit hypotheses preserve short exact
projective-cover sequences, and projective preservation carries their middle terms to
projectives. -/
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

/-- Let R,S be rings in independent universes uR,uS, with module universes vR,vS. Assume R can be
represented in vR, and F:R-Mod_{vR}→S-Mod_{vS} is additive, preserves finite limits and finite
colimits, and sends projective objects to projective objects. For M in R-Mod_{vR}, n∈ℕ and
pd(M)<n, one has pd(FM)<n. At n=0 the source object is zero and additivity carries it to zero.
At n=d+1 this is the corresponding non-strict bound pd(M)≤d. -/
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

/-- Let R,S be rings in universes uR,uS, representable in their respective module universes vR,vS.
Let E:R-Mod_{vR}≅S-Mod_{vS} be an equivalence whose forward and inverse functors are additive.
For M in R-Mod_{vR} and n∈ℕ, pd(E(M))<n if and only if pd(M)<n. The forward and inverse
equivalences preserve exact sequences and projectives, and the equivalence unit identifies the
twice-transported module with M. -/
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

/-- Let R,S be rings in universes uR,uS, representable in their respective module universes vR,vS.
Let E:R-Mod_{vR}≅S-Mod_{vS} be an equivalence whose forward and inverse functors are additive.
For M in R-Mod_{vR} and n∈ℕ, pd(E(M))≤n if and only if pd(M)≤n. This is the strict-bound
comparison at n+1, with the same module and equivalence data. -/
theorem hasProjectiveDimensionLE_equivalence_iff (M : ModuleCat.{vR} R) (n : ℕ) :
    HasProjectiveDimensionLE (E.functor.obj M) n ↔ HasProjectiveDimensionLE M n :=
  hasProjectiveDimensionLT_equivalence_iff E M (n + 1)

/-- Let R,S be rings in universes uR,uS, representable in their respective module universes vR,vS.
Let E:R-Mod_{vR}≅S-Mod_{vS} be an equivalence whose forward and inverse functors are additive.
For M in R-Mod_{vR}, the numeric projective dimensions satisfy pd(E(M))=pd(M). The equality is
in the extended naturals with an extra bottom value, so it retains finite dimensions, infinite
dimension and the zero-object bottom value. -/
theorem projectiveDimension_equivalence (M : ModuleCat.{vR} R) :
    projectiveDimension (E.functor.obj M) = projectiveDimension M := by
  simp only [projectiveDimension]
  congr! 5
  exact hasProjectiveDimensionLT_equivalence_iff E M _

end AdditiveEquivalence

end ModuleCat

end
