/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.CurveVectorBundles
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.CurveVectorBundles

universe u

variable {k : Type u} [Field k] {X : Scheme.{u}}

-- Rank-one vector bundles are exactly the invertible sheaves.
example (L : X.Modules) (hL : IsLineBundle L) : IsVectorBundle L 1 :=
  (isVectorBundle_one_iff L).2 hL

example (L : X.Modules) (hL : IsVectorBundle L 1) : IsLineBundle L :=
  (isVectorBundle_one_iff L).1 hL

-- On an invertible sheaf the bundle degree is the line-bundle degree, so there is a
-- single notion of degree.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f] (L : X.Modules) (hL : IsLineBundle L) :
    bundleDegree f L 1 ((isVectorBundle_one_iff L).2 hL) = degree f L hL :=
  bundleDegree_eq_degree f L _ hL

-- The structure sheaf, as a rank-one bundle, has degree zero and slope zero.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f] :
    bundleDegree f (structureModule X) 1
      ((isVectorBundle_one_iff _).2 (isLineBundle_structureModule X)) = 0 := by
  rw [bundleDegree_eq_degree f _ _ (isLineBundle_structureModule X), degree_structureModule]

example (f : X ⟶ Spec (.of k)) [IsProperCurve f] :
    slope f (structureModule X) 1
      ((isVectorBundle_one_iff _).2 (isLineBundle_structureModule X)) one_pos = 0 := by
  simp [slope, bundleDegree_eq_degree f _ _ (isLineBundle_structureModule X)]

-- The degree is computed with the given rank: a rank-`r` bundle subtracts `r χ(𝒪)`.
example (f : X ⟶ Spec (.of k)) [IsProperCurve f] (E : X.Modules) (r : ℕ)
    (hE : IsVectorBundle E r) :
    bundleDegree f E r hE =
      ((Module.finrank k (cohomology f E 0) : ℤ) - Module.finrank k (cohomology f E 1)) -
        r * ((Module.finrank k (cohomology f (structureModule X) 0) : ℤ) -
          Module.finrank k (cohomology f (structureModule X) 1)) := rfl

-- Global generation is the existence of generating global sections, with no finiteness
-- condition: every free sheaf is globally generated, on any index type.
-- A vector bundle of rank zero is the zero module: every section vanishes.
example (E : X.Modules) (hE : IsVectorBundle E 0) (U : X.Opens) (s : Γ(E, U)) : s = 0 := by
  have h := congrArg (fun φ ↦ Scheme.Modules.Hom.app φ U s)
    ((isZero_of_isVectorBundle_zero hE).eq_of_src (𝟙 E) 0)
  simpa using h

-- Conversely the zero module is a vector bundle of rank zero.
example (E : X.Modules) (hE : IsZero E) : IsVectorBundle E 0 := fun _ ↦
  ⟨⊤, trivial, ⟨((Scheme.Modules.pullback (⊤ : X.Opens).ι).map_isZero hE).iso
    (isZero_trivialBundle_zero _)⟩⟩

example (I : Type u) : GloballyGenerated (SheafOfModules.free (R := X.ringCatSheaf) I) :=
  ⟨SheafOfModules.free.generatingSections I⟩
