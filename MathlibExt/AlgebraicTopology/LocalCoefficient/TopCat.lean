/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSet
public import
  MathlibExt.Topology.Homotopy.TopCat.SingularFundamentalGroupoid

/-!
# Local-coefficient chains on a topological space

A covariant local system on a topological space is a module-valued functor
from its topological fundamental groupoid.  Pulling it back along the
canonical functor from the fundamental groupoid of the singular simplicial
set gives the simplicial module and unnormalized alternating-face complex
constructed for simplicial sets.

The edge formula uses the forward singular path and contains no inverse.
This file stops before maps of spaces, normalized chains, homology,
constant-coefficient comparison, acyclicity, and plus constructions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe uR uX

namespace TopCat

/-- A covariant local system of `R`-modules on a topological space. -/
abbrev LocalSystem (R : Type uR) [CommRing R] (X : TopCat.{uX}) :=
  _root_.FundamentalGroupoid X ⥤ ModuleCat.{max uR uX} R

namespace LocalSystem

variable {R : Type uR} [CommRing R] {X : TopCat.{uX}}

/-- Pull a topological local system back to the fundamental groupoid of the
singular simplicial set using the canonical forward comparison functor. -/
noncomputable def toSingular (L : TopCat.LocalSystem R X) :
    SSet.LocalSystem R (TopCat.toSSet.obj X) :=
  TopCat.singularFundamentalGroupoidFunctor X ⋙ L

/-- The singular pullback evaluates a represented singular vertex at the
point represented by that vertex. -/
@[simp]
theorem toSingular_obj_mk (L : TopCat.LocalSystem R X)
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    L.toSingular.obj (SSet.FundamentalGroupoid.mk x) =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) := by
  change L.obj ((TopCat.singularFundamentalGroupoidFunctor X).obj
    (SSet.FundamentalGroupoid.mk x)) = _
  rw [TopCat.singularFundamentalGroupoidFunctor_obj_mk]

/-- The singular pullback sends an edge generator to the local-system action
of the corresponding forward singular path. -/
@[simp]
theorem toSingular_map_homMk (L : TopCat.LocalSystem R X)
    {x y : (TopCat.toSSet.obj X) _⦋0⦌}
    (e : (TopCat.toSSet.obj X).Edge x y) :
    L.toSingular.map (SSet.FundamentalGroupoid.homMk e) =
      L.map (Path.Homotopic.Quotient.mk
        ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
          (TopCat.counit_realizedVertex x)
          (TopCat.counit_realizedVertex y))) := by
  change L.map ((TopCat.singularFundamentalGroupoidFunctor X).map
    (SSet.FundamentalGroupoid.homMk e)) = _
  exact congrArg L.map
    (TopCat.singularFundamentalGroupoidFunctor_map_homMk X e)

end LocalSystem

section Coefficients

variable {R : Type uR} [CommRing R] {X : TopCat.{uX}}
variable (L : TopCat.LocalSystem R X)

/-- The coefficient family on degree-`n` singular simplices. -/
noncomputable abbrev localCoefficientFamily (n : ℕ) :
    (TopCat.toSSet.obj X) _⦋n⦌ → ModuleCat.{max uR uX} R :=
  SSet.localCoefficientFamily L.toSingular n

/-- Degree zero evaluates the local system at the represented point. -/
@[simp]
theorem localCoefficientFamily_zero
    (x : (TopCat.toSSet.obj X) _⦋0⦌) :
    localCoefficientFamily L 0 x =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) := by
  unfold localCoefficientFamily
  rw [SSet.localCoefficientFamily_zero]
  exact LocalSystem.toSingular_obj_mk L x

/-- Degree-`n` unnormalized local-coefficient chains. -/
noncomputable abbrev localCoefficientObj (n : ℕ) :
    ModuleCat.{max uR uX} R :=
  SSet.localCoefficientObj L.toSingular n

/-- The local-coefficient map induced by a face of the singular simplicial
set. -/
noncomputable abbrev localCoefficientFace {n : ℕ}
    (i : Fin (n + 2)) :
    localCoefficientObj L (n + 1) ⟶ localCoefficientObj L n :=
  SSet.localCoefficientFace L.toSingular i

/-- The local-coefficient map induced by a degeneracy of the singular
simplicial set. -/
noncomputable abbrev localCoefficientDegeneracy {n : ℕ}
    (i : Fin (n + 1)) :
    localCoefficientObj L n ⟶ localCoefficientObj L (n + 1) :=
  SSet.localCoefficientDegeneracy L.toSingular i

/-- The simplicial module of singular chains with local coefficients. -/
noncomputable def localCoefficientSimplicial :
    SimplicialObject (ModuleCat.{max uR uX} R) :=
  SSet.localCoefficientSimplicial L.toSingular

/-- Formula for a degree object of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_obj (n : ℕ) :
    (localCoefficientSimplicial L).obj
        (op (SimplexCategory.mk n)) =
      localCoefficientObj L n :=
  SSet.localCoefficientSimplicial_obj L.toSingular n

/-- Formula for a face of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_map_δ {n : ℕ}
    (i : Fin (n + 2)) :
    (localCoefficientSimplicial L).map
        (SimplexCategory.δ i).op =
      localCoefficientFace L i :=
  SSet.localCoefficientSimplicial_map_δ L.toSingular i

/-- Formula for a degeneracy of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_map_σ {n : ℕ}
    (i : Fin (n + 1)) :
    (localCoefficientSimplicial L).map
        (SimplexCategory.σ i).op =
      localCoefficientDegeneracy L i :=
  SSet.localCoefficientSimplicial_map_σ L.toSingular i

/-- The unnormalized alternating-face complex of singular chains with local
coefficients. -/
noncomputable def localCoefficientChainComplex :
    ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  SSet.localCoefficientChainComplex L.toSingular

/-- Formula for a degree object of the local-coefficient chain complex. -/
@[simp]
theorem localCoefficientChainComplex_X (n : ℕ) :
    (localCoefficientChainComplex L).X n =
      localCoefficientObj L n :=
  SSet.localCoefficientChainComplex_X L.toSingular n

/-- The differential is the alternating sum of the singular face maps with
local coefficients. -/
theorem localCoefficientChainComplex_d (n : ℕ) :
    (localCoefficientChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        localCoefficientFace L i :=
  SSet.localCoefficientChainComplex_d L.toSingular n

end Coefficients

end TopCat
