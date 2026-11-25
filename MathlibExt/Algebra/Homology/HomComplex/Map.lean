/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.HomComplex.LinearMap

/-!
# Maps of Hom complexes

Precomposition and postcomposition on `HomComplex` cochains assemble
into a two-variable cochain map by the differential naturality laws.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace CochainComplex.HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {F F' F'' G G' G'' : CochainComplex C ℤ}

/-- Literal precomposition by f and postcomposition by g, on cochains. -/
def mapLinear (f : F' ⟶ F) (g : G ⟶ G') (n : ℤ) :
    Cochain F G n →ₗ[ℤ] Cochain F' G' n :=
  mapLinearOver ℤ f g n

/-- The pointwise map retains the two morphism components. -/
@[simp]
theorem mapLinear_v (f : F' ⟶ F) (g : G ⟶ G') (n p q : ℤ)
    (hpq : p + n = q) (z : Cochain F G n) :
    (mapLinear f g n z).v p q hpq = f.f p ≫ z.v p q hpq ≫ g.f q := by
  exact mapLinearOver_v ℤ f g n p q hpq z

/-- Differential naturality; no relation or exactness premise is required. -/
theorem mapLinear_δ (f : F' ⟶ F) (g : G ⟶ G') (n m : ℤ)
    (z : Cochain F G n) :
    mapLinear f g m (δ n m z) = δ n m (mapLinear f g n z) := by
  exact mapLinearOver_δ ℤ f g n m z

/-- The Hom-complex morphism induced by the two complex maps. -/
def map (f : F' ⟶ F) (g : G ⟶ G') : HomComplex F G ⟶ HomComplex F' G' where
  f n := AddCommGrpCat.ofHom (mapLinear f g n).toAddMonoidHom
  comm' i j hij := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro z
    change δ i j (mapLinear f g i z) = mapLinear f g j (δ i j z)
    exact (mapLinear_δ f g i j z).symm

@[simp]
theorem map_f (f : F' ⟶ F) (g : G ⟶ G') (n : ℤ) :
    (map f g).f n = AddCommGrpCat.ofHom (mapLinear f g n).toAddMonoidHom := rfl

/-- Identities act as the identity on the Hom complex. -/
@[simp]
theorem map_id (F G : CochainComplex C ℤ) : map (𝟙 F) (𝟙 G) = 𝟙 (HomComplex F G) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  change mapLinearOver ℤ (𝟙 F) (𝟙 G) n z = z
  exact congrArg (fun h : Cochain F G n →ₗ[ℤ] Cochain F G n => h z)
    (mapLinearOver_id ℤ F G n)

/-- Composition has the contravariant/covariant order. -/
theorem map_comp (f : F' ⟶ F) (f' : F'' ⟶ F') (g : G ⟶ G') (g' : G' ⟶ G'') :
    map f g ≫ map f' g' = map (f' ≫ f) (g ≫ g') := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro z
  change mapLinearOver ℤ f' g' n (mapLinearOver ℤ f g n z) =
    mapLinearOver ℤ (f' ≫ f) (g ≫ g') n z
  exact congrArg (fun h : Cochain F G n →ₗ[ℤ] Cochain F'' G'' n => h z)
    (mapLinearOver_comp ℤ f f' g g' n)

end CochainComplex.HomComplex
