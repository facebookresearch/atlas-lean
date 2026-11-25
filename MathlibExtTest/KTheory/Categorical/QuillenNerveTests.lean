/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.Category.ModuleCat.Biproducts
import MathlibExt.CategoryTheory.ExactCategory.Abelian
import MathlibExt.KTheory.Exact.Quillen.Nerve

/-!
# Quillen Q-nerve consumer tests

Consumer-style checks for the public unpointed nerve `NQ` over `ModuleCat ℚ`:
zero-vertex 0-simplex type, identity and composition laws, 0-simplex mapping,
representative 1-simplex formula, and natural-isomorphism homotopy type.
No implementation details are unfolded; no pointed realization, loop space,
higher K-groups, weak-equivalence, Q/S comparison, spectrum, or Milnor/Bloch-Kato
claim is made.
-/

open CategoryTheory
open CategoryTheory.Limits
open Simplicial Opposite

/-- Zero vertex has the expected 0-simplex type. -/
noncomputable example : (AlgebraicKTheory.NQ (ModuleCat ℚ)).obj (op ⦋0⦌) :=
  AlgebraicKTheory.NQ.zeroVertex (ModuleCat ℚ)

/-- Identity exact functor acts as the identity on nerves. -/
example : AlgebraicKTheory.NQ.map (𝟭 (ModuleCat ℚ)) =
    𝟙 (AlgebraicKTheory.NQ (ModuleCat ℚ)) :=
  AlgebraicKTheory.NQ.map_id

/-- Exact-functor composition acts as nerve-map composition. -/
example (F G : ModuleCat ℚ ⥤ ModuleCat ℚ) [F.Additive] [G.Additive]
    [F.IsExact] [G.IsExact] :
    AlgebraicKTheory.NQ.map F ≫ AlgebraicKTheory.NQ.map G =
      AlgebraicKTheory.NQ.map (F ⋙ G) :=
  AlgebraicKTheory.NQ.map_comp F G

/-- Nerve maps send 0-simplices to 0-simplices pointwise. -/
example (F : ModuleCat ℚ ⥤ ModuleCat ℚ) [F.Additive] [F.IsExact]
    (X : AlgebraicKTheory.QuillenQ (ModuleCat ℚ)) :
    (AlgebraicKTheory.NQ.map F).app (op ⦋0⦌) (ComposableArrows.mk₀ X) =
      ComposableArrows.mk₀ ((AlgebraicKTheory.QuillenQ.map F).obj X) :=
  AlgebraicKTheory.NQ.map_app_mk₀ F X

/-- Representative 1-simplex formula (repaired regression). -/
example (F : ModuleCat ℚ ⥤ ModuleCat ℚ) [F.Additive] [F.IsExact]
    {X Y : AlgebraicKTheory.QuillenQ (ModuleCat ℚ)}
    (S : AlgebraicKTheory.QuillenSpan X.obj Y.obj) :
    (AlgebraicKTheory.NQ.map F).app (op ⦋1⦌)
        (ComposableArrows.mk₁ (AlgebraicKTheory.QuillenQ.mkHom S)) =
      ComposableArrows.mk₁
        (AlgebraicKTheory.QuillenQ.mkHom (AlgebraicKTheory.QuillenSpan.map F S)) :=
  AlgebraicKTheory.NQ.map_app_mk₁_mkHom F S

/-- Natural-isomorphism transport has the intended homotopy type. -/
noncomputable example (F G : ModuleCat ℚ ⥤ ModuleCat ℚ) [F.Additive]
    [G.Additive] [F.IsExact] [G.IsExact] (e : F ≅ G) :
    SSet.Homotopy (AlgebraicKTheory.NQ.map F) (AlgebraicKTheory.NQ.map G) :=
  AlgebraicKTheory.NQ.mapNatIsoHomotopy F G e
