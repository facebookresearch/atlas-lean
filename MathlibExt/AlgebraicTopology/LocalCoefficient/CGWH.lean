/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.TopCat
public import MathlibExt.Topology.Category.CGWH.Basic

/-!
# Local-coefficient chains on a CGWH space

Local systems and their unnormalized singular chain complexes on a compactly
generated weak Hausdorff space are the corresponding TopCat constructions on
the underlying topological space.  The compact-generation universe does not
enter the coefficient-module universe.

This is a thin wrapper.  It adds no map of spaces, normalized chains,
homology, constant-coefficient comparison, acyclicity, or plus-construction
claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite
open scoped Simplicial

universe uR uK uX

namespace CGWH

/-- A local system on a CGWH space is a local system on its underlying
topological space. -/
abbrev LocalSystem (R : Type uR) [CommRing R]
    (X : CGWH.{uK, uX}) :=
  TopCat.LocalSystem R X.toTop

namespace LocalSystem

variable {R : Type uR} [CommRing R] {X : CGWH.{uK, uX}}

/-- Pull a CGWH local system back to the fundamental groupoid of the
singular simplicial set of the underlying topological space. -/
noncomputable abbrev toSingular (L : CGWH.LocalSystem R X) :
    SSet.LocalSystem R (TopCat.toSSet.obj X.toTop) :=
  TopCat.LocalSystem.toSingular L

/-- The singular pullback evaluates a represented vertex at its underlying
point. -/
@[simp]
theorem toSingular_obj_mk (L : CGWH.LocalSystem R X)
    (x : (TopCat.toSSet.obj X.toTop) _⦋0⦌) :
    L.toSingular.obj (SSet.FundamentalGroupoid.mk x) =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) :=
  TopCat.LocalSystem.toSingular_obj_mk L x

/-- The singular pullback acts on an edge by the corresponding forward
singular path in the underlying topological space. -/
@[simp]
theorem toSingular_map_homMk (L : CGWH.LocalSystem R X)
    {x y : (TopCat.toSSet.obj X.toTop) _⦋0⦌}
    (e : (TopCat.toSSet.obj X.toTop).Edge x y) :
    L.toSingular.map (SSet.FundamentalGroupoid.homMk e) =
      L.map (Path.Homotopic.Quotient.mk
        ((TopCat.pathEquiv (TopCat.singularEdgePath e)).cast
          (TopCat.counit_realizedVertex x)
          (TopCat.counit_realizedVertex y))) :=
  TopCat.LocalSystem.toSingular_map_homMk L e

end LocalSystem

section Coefficients

variable {R : Type uR} [CommRing R] {X : CGWH.{uK, uX}}
variable (L : CGWH.LocalSystem R X)

/-- The coefficient family on degree-`n` singular simplices. -/
noncomputable abbrev localCoefficientFamily (n : ℕ) :
    (TopCat.toSSet.obj X.toTop) _⦋n⦌ →
      ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientFamily L n

/-- Degree zero evaluates the local system at the represented point. -/
@[simp]
theorem localCoefficientFamily_zero
    (x : (TopCat.toSSet.obj X.toTop) _⦋0⦌) :
    localCoefficientFamily L 0 x =
      L.obj (_root_.FundamentalGroupoid.mk
        (TopCat.toSSetObj₀Equiv x)) :=
  TopCat.localCoefficientFamily_zero L x

/-- Degree-`n` unnormalized local-coefficient chains. -/
noncomputable abbrev localCoefficientObj (n : ℕ) :
    ModuleCat.{max uR uX} R :=
  TopCat.localCoefficientObj L n

/-- The local-coefficient map induced by a singular face. -/
noncomputable abbrev localCoefficientFace {n : ℕ}
    (i : Fin (n + 2)) :
    localCoefficientObj L (n + 1) ⟶ localCoefficientObj L n :=
  TopCat.localCoefficientFace L i

/-- The local-coefficient map induced by a singular degeneracy. -/
noncomputable abbrev localCoefficientDegeneracy {n : ℕ}
    (i : Fin (n + 1)) :
    localCoefficientObj L n ⟶ localCoefficientObj L (n + 1) :=
  TopCat.localCoefficientDegeneracy L i

/-- The simplicial module of singular chains with local coefficients. -/
noncomputable def localCoefficientSimplicial :
    SimplicialObject (ModuleCat.{max uR uX} R) :=
  TopCat.localCoefficientSimplicial L

/-- Formula for a degree object of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_obj (n : ℕ) :
    (localCoefficientSimplicial L).obj
        (op (SimplexCategory.mk n)) =
      localCoefficientObj L n :=
  TopCat.localCoefficientSimplicial_obj L n

/-- Formula for a face of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_map_δ {n : ℕ}
    (i : Fin (n + 2)) :
    (localCoefficientSimplicial L).map
        (SimplexCategory.δ i).op =
      localCoefficientFace L i :=
  TopCat.localCoefficientSimplicial_map_δ L i

/-- Formula for a degeneracy of the local-coefficient simplicial module. -/
@[simp]
theorem localCoefficientSimplicial_map_σ {n : ℕ}
    (i : Fin (n + 1)) :
    (localCoefficientSimplicial L).map
        (SimplexCategory.σ i).op =
      localCoefficientDegeneracy L i :=
  TopCat.localCoefficientSimplicial_map_σ L i

/-- The unnormalized alternating-face complex of singular chains with local
coefficients. -/
noncomputable def localCoefficientChainComplex :
    ChainComplex (ModuleCat.{max uR uX} R) ℕ :=
  TopCat.localCoefficientChainComplex L

/-- Formula for a degree object of the local-coefficient chain complex. -/
@[simp]
theorem localCoefficientChainComplex_X (n : ℕ) :
    (localCoefficientChainComplex L).X n =
      localCoefficientObj L n :=
  TopCat.localCoefficientChainComplex_X L n

/-- The differential is the alternating sum of the singular face maps with
local coefficients. -/
theorem localCoefficientChainComplex_d (n : ℕ) :
    (localCoefficientChainComplex L).d (n + 1) n =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ (i : ℕ) •
        localCoefficientFace L i :=
  TopCat.localCoefficientChainComplex_d L n

end Coefficients

end CGWH
