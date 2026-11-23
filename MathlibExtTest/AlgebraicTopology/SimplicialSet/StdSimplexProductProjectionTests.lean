/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexProductProjection

/-!
# Standard-simplex product-projection tests

These tests pin the last-vertex section, the direction and stationary second
coordinate of its contraction, and the exact forward and inverse realized
maps.  Both dimensions zero and one exercise the weak-equivalence theorem.
-/

open CategoryTheory Limits CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.StdSimplexProductProjectionTests

universe u

variable (m : ℕ) (T : SSet.{u})

example :
    SSet.stdSimplexProdLastSection m T ≫ fst _ _ =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m)) :=
  SSet.stdSimplexProdLastSection_fst m T

example : SSet.stdSimplexProdLastSection m T ≫ snd _ _ = 𝟙 T :=
  SSet.stdSimplexProdLastSection_snd m T

/-- The contraction is deliberately identity-to-retraction, not reversed. -/
noncomputable example :
    SSet.Homotopy
      (𝟙 ((Δ[m] : SSet.{u}) ⊗ T))
      ((snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T) ≫
        SSet.stdSimplexProdLastSection m T) :=
  SSet.stdSimplexProdContraction m T

example :
    (SSet.stdSimplexProdContraction m T).h ≫ snd _ _ =
      fst _ _ ≫ snd _ _ :=
  SSet.stdSimplexProdContraction_h_snd m T

section Realization

variable (T₀ : SSet.{u})

example :
    (SSet.realizedStdSimplexProdSndHomotopyEquiv m T₀).toFun =
      (SSet.toTop.map
        (snd _ _ : (Δ[m] : SSet.{u}) ⊗ T₀ ⟶ T₀)).hom :=
  SSet.realizedStdSimplexProdSndHomotopyEquiv_toFun m T₀

example :
    (SSet.realizedStdSimplexProdSndHomotopyEquiv m T₀).invFun =
      (SSet.toTop.map (SSet.stdSimplexProdLastSection m T₀)).hom :=
  SSet.realizedStdSimplexProdSndHomotopyEquiv_invFun m T₀

example :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        (prod.snd : (Δ[0] : SSet.{u}) ⨯ T₀ ⟶ T₀)) :=
  SSet.stdSimplexProdSnd_mem_weakHomotopyEquivalences 0 T₀

example :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        (prod.snd : (Δ[1] : SSet.{u}) ⨯ T₀ ⟶ T₀)) :=
  SSet.stdSimplexProdSnd_mem_weakHomotopyEquivalences 1 T₀

end Realization

end MathlibExtTest.AlgebraicTopology.SimplicialSet.StdSimplexProductProjectionTests
