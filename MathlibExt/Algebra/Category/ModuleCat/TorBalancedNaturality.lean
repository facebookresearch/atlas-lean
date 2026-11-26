/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TorBalancedUniverse

/-!
# Naturality of the symmetry of Tor

For a commutative ring `R : Type u`, the balanced tensor symmetry gives `Tor_q^R(M, N) ≅
Tor_q^R(N, M)` for modules with carriers in universe `max u v`.

For morphisms `f : M₁ ⟶ M₂` and `g : N₁ ⟶ N₂`, the forward symmetry intertwines `Tor_q(f, g)`
with `Tor_q(g, f)`. The inverse symmetry satisfies the corresponding reversed square. Both
statements retain the chosen tensor and derived-functor coordinates.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor

namespace ModuleCat.UniverseTensor

universe u v

variable (R : Type u) [CommRing R]

/-- Forward Tor symmetry is natural in both module variables.

For module maps `f : M₁ ⟶ M₂` and `g : N₁ ⟶ N₂`, the map `Tor_q(f, g)` followed by the forward
symmetry at `(M₂, N₂)` equals the forward symmetry at `(M₁, N₁)` followed by `Tor_q(g, f)`. -/
theorem nativeTorSymmetry_hom_naturality
    {M₁ M₂ N₁ N₂ : ModuleCat.{max u v} R} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v}
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v}
    letI : SymmetricCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.symmetricCategory.{u,v}
    (((Tor (ModuleCat.{max u v} R) q).map f).app N₁ ≫
        ((Tor (ModuleCat.{max u v} R) q).obj M₂).map g) ≫
        (nativeTorSymmetry.{u,v} R M₂ N₂ q).hom =
      (nativeTorSymmetry.{u,v} R M₁ N₁ q).hom ≫
        ((Tor (ModuleCat.{max u v} R) q).map g).app M₁ ≫
        ((Tor (ModuleCat.{max u v} R) q).obj N₂).map f := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v} R) := tensorStructure.{u,v}
  let : MonoidalCategory (ModuleCat.{max u v} R) := monoidalCategory.{u,v}
  let : MonoidalPreadditive (ModuleCat.{max u v} R) := monoidalPreadditive.{u,v}
  let : SymmetricCategory (ModuleCat.{max u v} R) := symmetricCategory.{u,v}
  let T := Tor (ModuleCat.{max u v} R) q
  let E := nativeTorSymmetryNatIso.{u,v} R q
  have hF : (T.map f).app N₁ ≫ ((E.app M₂).app N₁).hom =
      ((E.app M₁).app N₁).hom ≫ (T.obj N₁).map f := by
    exact congrArg (fun t => t.app N₁) (E.hom.naturality f)
  have hG : (T.obj M₂).map g ≫ ((E.app M₂).app N₂).hom =
      ((E.app M₂).app N₁).hom ≫ (T.map g).app M₂ :=
    (E.app M₂).hom.naturality g
  change ((T.map f).app N₁ ≫ (T.obj M₂).map g) ≫ ((E.app M₂).app N₂).hom =
    ((E.app M₁).app N₁).hom ≫ (T.map g).app M₁ ≫ (T.obj N₂).map f
  calc
    _ = (T.map f).app N₁ ≫ ((E.app M₂).app N₁).hom ≫ (T.map g).app M₂ := by
      simpa only [Category.assoc] using congrArg (fun t => (T.map f).app N₁ ≫ t) hG
    _ = ((E.app M₁).app N₁).hom ≫ (T.obj N₁).map f ≫ (T.map g).app M₂ := by
      simpa only [Category.assoc] using congrArg (fun t => t ≫ (T.map g).app M₂) hF
    _ = _ := by
      simpa only [Category.assoc] using congrArg
        (fun t => ((E.app M₁).app N₁).hom ≫ t) ((T.map g).naturality f)

/-- Inverse Tor symmetry is natural in both module variables.

For the same module maps, `Tor_q(g, f)` followed by the inverse symmetry at `(M₂, N₂)` equals
the inverse symmetry at `(M₁, N₁)` followed by `Tor_q(f, g)`. -/
theorem nativeTorSymmetry_inv_naturality
    {M₁ M₂ N₁ N₂ : ModuleCat.{max u v} R} (f : M₁ ⟶ M₂) (g : N₁ ⟶ N₂) (q : ℕ) :
    letI : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.tensorStructure.{u,v}
    letI : MonoidalCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalCategory.{u,v}
    letI : MonoidalPreadditive (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.monoidalPreadditive.{u,v}
    letI : SymmetricCategory (ModuleCat.{max u v} R) :=
      ModuleCat.UniverseTensor.symmetricCategory.{u,v}
    (((Tor (ModuleCat.{max u v} R) q).map g).app M₁ ≫
        ((Tor (ModuleCat.{max u v} R) q).obj N₂).map f) ≫
        (nativeTorSymmetry.{u,v} R M₂ N₂ q).inv =
      (nativeTorSymmetry.{u,v} R M₁ N₁ q).inv ≫
        ((Tor (ModuleCat.{max u v} R) q).map f).app N₁ ≫
        ((Tor (ModuleCat.{max u v} R) q).obj M₂).map g := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.tensorStructure.{u,v}
  let : MonoidalCategory (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalCategory.{u,v}
  let : MonoidalPreadditive (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.monoidalPreadditive.{u,v}
  let : SymmetricCategory (ModuleCat.{max u v} R) :=
    ModuleCat.UniverseTensor.symmetricCategory.{u,v}
  rw [← cancel_mono (nativeTorSymmetry.{u,v} R M₂ N₂ q).hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have hn := congrArg (fun k => (nativeTorSymmetry.{u,v} R M₁ N₁ q).inv ≫ k)
    (nativeTorSymmetry_hom_naturality.{u,v} R f g q)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hn.symm

end ModuleCat.UniverseTensor
