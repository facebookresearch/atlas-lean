/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.CGWH
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetConstant
public import MathlibExt.AlgebraicTopology.LocalCoefficient.SSetFunctoriality
public import Mathlib.AlgebraicTopology.SingularHomology.Basic

/-!
# Constant local systems on TopCat and CGWH spaces

The singular pullback of a native constant topological local system is
canonically isomorphic to the literal constant local system on the singular
fundamental groupoid.  Functoriality in the local system transports this Iso
to chains, and the simplicial-set constant comparison then identifies the
result with the existing singular chain complex.  CGWH receives only a thin
wrapper through its underlying TopCat object.

This file stops before homology, maps of spaces, local-coefficient
equivalences, acyclicity, or plus constructions.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.style.longLine false

noncomputable section

open CategoryTheory Limits Opposite
open scoped Simplicial

universe uR uK uX

namespace TopCat

variable {R : Type uR} [CommRing R]
variable {X : TopCat.{uX}}
variable (M : ModuleCat.{max uR uX} R)

/-- The native topological constant local system with value `M`. -/
abbrev constantLocalSystem : TopCat.LocalSystem R X :=
  (Functor.const (_root_.FundamentalGroupoid X)).obj M

namespace LocalSystem

/-- The singular pullback of a native constant system is canonically
isomorphic to the literal constant system on the singular fundamental
groupoid. -/
noncomputable def constantToSingularIso :
    (TopCat.constantLocalSystem (X := X) M).toSingular ≅
      SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro x y f
    change 𝟙 M ≫ 𝟙 M = 𝟙 M ≫ 𝟙 M
    simp)

@[simp]
theorem constantToSingularIso_hom_app
    (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (constantToSingularIso M).hom.app x = 𝟙 M :=
  rfl

@[simp]
theorem constantToSingularIso_inv_app
    (x : SSet.FundamentalGroupoid (TopCat.toSSet.obj X)) :
    (constantToSingularIso M).inv.app x = 𝟙 M :=
  rfl

end LocalSystem

/-- Chain-level comparison between the singular pullback of the native
constant system and the literal constant singular local system. -/
noncomputable def constantToSingularChainIso :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X) M) ≅
      SSet.localCoefficientChainComplex
        (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M) := by
  change (SSet.localCoefficientChainComplexFunctor
      (R := R) (X := TopCat.toSSet.obj X)).obj
        (TopCat.constantLocalSystem (X := X) M).toSingular ≅
    (SSet.localCoefficientChainComplexFunctor
      (R := R) (X := TopCat.toSSet.obj X)).obj
        (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M)
  exact (SSet.localCoefficientChainComplexFunctor
    (R := R) (X := TopCat.toSSet.obj X)).mapIso
      (TopCat.LocalSystem.constantToSingularIso M)

@[simp]
theorem constantToSingularChainIso_hom_f (n : ℕ) :
    (constantToSingularChainIso (X := X) M).hom.f n =
      SSet.localCoefficientMap
        (X := TopCat.toSSet.obj X)
        (TopCat.LocalSystem.constantToSingularIso (X := X) M).hom n := by
  change ((SSet.localCoefficientChainComplexFunctor
      (R := R) (X := TopCat.toSSet.obj X)).map
        (TopCat.LocalSystem.constantToSingularIso (X := X) M).hom).f n = _
  rw [SSet.localCoefficientChainComplexFunctor_map,
    SSet.localCoefficientChainMap_f]

/-- Native constant local-coefficient chains agree with the existing singular
chain complex. -/
noncomputable def constantLocalCoefficientChainIso :
    TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{max uR uX} R)).obj M).obj X := by
  change TopCat.localCoefficientChainComplex
        (TopCat.constantLocalSystem (X := X) M) ≅
      (TopCat.toSSet.obj X).chainComplex M
  exact constantToSingularChainIso M ≪≫
    SSet.constantLocalCoefficientChainIso
      (X := TopCat.toSSet.obj X) M

@[simp]
theorem constantLocalCoefficientChainIso_hom_f (n : ℕ) :
    (constantLocalCoefficientChainIso (X := X) M).hom.f n =
      SSet.localCoefficientMap
          (X := TopCat.toSSet.obj X)
          (TopCat.LocalSystem.constantToSingularIso (X := X) M).hom n ≫
        (SSet.constantLocalCoefficientChainIso
          (X := TopCat.toSSet.obj X) M).hom.f n :=
  rfl

/-- Inclusion of a singular simplex summand for the native constant local
system. -/
noncomputable abbrev constantLocalCoefficientι {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    M ⟶ TopCat.localCoefficientObj
      (TopCat.constantLocalSystem (X := X) M) n :=
  SSet.localCoefficientι
    (TopCat.constantLocalSystem (X := X) M).toSingular σ

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The constant comparison sends every native local-coefficient summand to
the corresponding ordinary singular-chain summand. -/
@[reassoc (attr := simp)]
theorem constantLocalCoefficientι_comp_chainIso_hom {n : ℕ}
    (σ : (TopCat.toSSet.obj X) _⦋n⦌) :
    constantLocalCoefficientι M σ ≫
        (constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (TopCat.toSSet.obj X).ιChainComplex σ := by
  rw [constantLocalCoefficientChainIso_hom_f, ← Category.assoc,
    SSet.localCoefficientι_map,
    TopCat.LocalSystem.constantToSingularIso_hom_app]
  let c := (SSet.constantLocalCoefficientChainIso
    (X := TopCat.toSSet.obj X) M).hom.f n
  have hId : 𝟙 M ≫ SSet.localCoefficientι
      (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M) σ =
        SSet.localCoefficientι
          (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M) σ :=
    Category.id_comp _
  calc
    (𝟙 M ≫ SSet.localCoefficientι
          (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M) σ) ≫ c =
        SSet.localCoefficientι
          (SSet.constantLocalSystem (X := TopCat.toSSet.obj X) M) σ ≫ c :=
      congrArg (fun k => k ≫ c) hId
    _ = _ := SSet.constantLocalCoefficientι_comp_chainIso_hom
      (X := TopCat.toSSet.obj X) M σ

end TopCat

namespace CGWH

variable {R : Type uR} [CommRing R]
variable {X : CGWH.{uK, uX}}
variable (M : ModuleCat.{max uR uX} R)

/-- The native constant local system on a CGWH space. -/
abbrev constantLocalSystem : CGWH.LocalSystem R X :=
  TopCat.constantLocalSystem (X := X.toTop) M

/-- Constant local-coefficient chains on a CGWH space agree with ordinary
singular chains on its underlying TopCat object. -/
noncomputable abbrev constantLocalCoefficientChainIso :
    CGWH.localCoefficientChainComplex
        (CGWH.constantLocalSystem (X := X) M) ≅
      ((AlgebraicTopology.singularChainComplexFunctor
        (ModuleCat.{max uR uX} R)).obj M).obj X.toTop :=
  TopCat.constantLocalCoefficientChainIso (X := X.toTop) M

/-- Inclusion of a singular simplex summand for the CGWH constant local
system. -/
noncomputable abbrev constantLocalCoefficientι {n : ℕ}
    (σ : (TopCat.toSSet.obj X.toTop) _⦋n⦌) :
    M ⟶ CGWH.localCoefficientObj
      (CGWH.constantLocalSystem (X := X) M) n :=
  TopCat.constantLocalCoefficientι (X := X.toTop) M σ

@[simp]
theorem constantLocalCoefficientChainIso_hom_f (n : ℕ) :
    (CGWH.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (TopCat.constantLocalCoefficientChainIso (X := X.toTop) M).hom.f n :=
  rfl

@[reassoc (attr := simp)]
theorem constantLocalCoefficientι_comp_chainIso_hom {n : ℕ}
    (σ : (TopCat.toSSet.obj X.toTop) _⦋n⦌) :
    CGWH.constantLocalCoefficientι M σ ≫
        (CGWH.constantLocalCoefficientChainIso (X := X) M).hom.f n =
      (TopCat.toSSet.obj X.toTop).ιChainComplex σ :=
  TopCat.constantLocalCoefficientι_comp_chainIso_hom
    (X := X.toTop) M σ

end CGWH
