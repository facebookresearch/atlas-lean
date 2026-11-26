/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkGaloisAction
public import MathlibExt.AlgebraicGeometry.Sites.FieldFiniteEtaleBasis
public import MathlibExt.CategoryTheory.Sites.Point.Mates
public import Mathlib.GroupTheory.GroupAction.Hom
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Equivariant-function sheaves as invariant skyscrapers

Let Ω/k be a separable closure of fields in universe u, G = Gal(Ω/k),
and c = max(u, w). For a discrete continuous G-module M with abelian
coefficients in universe c, the presheaf Φ̃_M assigns to an étale k-scheme U
the group Map_G(U(Ω), M), with pointwise operations.

The point skyscraper S_M has all functions on the common lifted geometric
fiber. Its diagonal G-action is
(D_g s)(z) = g • s(g⁻¹ • z).
Its invariant sections are exactly Φ̃_M(U). Their presheaf is a sheaf,
and the invariant-skyscraper sheaf Φ(M) is the limit of this action diagram.

Restriction is precomposition by V(Ω) → U(Ω), and a coefficient morphism
M → N acts by postcomposition. These maps agree with the invariant limit
functor. For a finite étale k-algebra A, Φ(M)(Spec A) identifies with
Map_G(Hom_(k-alg)(A, Ω), M), compatibly with algebra and coefficient maps.
Neither the Galois group nor the coefficient modules need be finite.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The geometric lifts U(Ω) carry the left G-action induced by the
Galois fiber maps. Under an affine algebra description this is
postcomposition of an Ω-valued algebra map by g ∈ G. -/
instance fieldOriginalFiberMulAction (U : (Spec (.of k)).Etale) :
    MulAction Gal(Ω/k) ((fieldGeometricPoint k Ω).fiber.obj U) where
  smul g z := (fieldGaloisFiberMap k Ω g).app U z
  one_smul z := by
    change (fieldGaloisFiberMap k Ω (1 : Gal(Ω/k))).app U z = z
    rw [fieldGaloisFiberMap_one]
    rfl
  mul_smul g h z := by
    change (fieldGaloisFiberMap k Ω (g * h)).app U z =
      (fieldGaloisFiberMap k Ω g).app U ((fieldGaloisFiberMap k Ω h).app U z)
    rw [fieldGaloisFiberMap_mul]
    rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For an étale map r : V → U, the map V(Ω) → U(Ω), z ↦ r ∘ z,
is G-equivariant. It is the geometric-fiber map used for section restriction. -/
def fieldOriginalFiberMap {U V : (Spec (.of k)).Etale} (r : V ⟶ U) :
    (fieldGeometricPoint k Ω).fiber.obj V →[Gal(Ω/k)]
      (fieldGeometricPoint k Ω).fiber.obj U where
  toFun := (fieldGeometricPoint k Ω).fiber.map r
  map_smul' g z := by
    change (fieldGeometricPoint k Ω).fiber.map r ((fieldGaloisFiberMap k Ω g).app V z) =
      (fieldGaloisFiberMap k Ω g).app U ((fieldGeometricPoint k Ω).fiber.map r z)
    exact ((fieldGaloisFiberMap k Ω g).naturality_apply r z).symm

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, this is the abelian group Map_G(U(Ω), M) of
G-equivariant functions, with pointwise addition, negation and zero.
Its carrier is in universe c. -/
abbrev FieldEquivariantFunctions (U : (Spec (.of k)).Etale)
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) : Type (max u w) :=
  (fieldGeometricPoint k Ω).fiber.obj U →[Gal(Ω/k)] DiscreteAbelianAction.underlying M

@[nolint defsWithUnderscore] -- instance name; never referenced
instance fieldEquivariantFunctions_addCommGroup (U : (Spec (.of k)).Etale)
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    AddCommGroup (FieldEquivariantFunctions.{u, w} k Ω U M) := by
  infer_instance

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D and r : V → U étale, restriction is the additive map
Map_G(U(Ω), M) → Map_G(V(Ω), M), h ↦ h ∘ r_Ω. -/
def fieldEquivariantFunctionsRestrict {U V : (Spec (.of k)).Etale} (r : V ⟶ U)
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    FieldEquivariantFunctions.{u, w} k Ω U M →+
      FieldEquivariantFunctions.{u, w} k Ω V M where
  toFun h := h.comp (fieldOriginalFiberMap k Ω r)
  map_zero' := by ext z; rfl
  map_add' h h' := by ext z; rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D and an étale map r : V → U, the restriction operator
on equivariant sections sends h to z ↦ h(r_Ω(z)). -/
@[deprecated fieldEquivariantFunctionsRestrict (since := "2026-10-28"), nolint defsWithUnderscore]
alias fieldEquivariantFunctions_restrict := fieldEquivariantFunctionsRestrict

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For an equivariant additive map t : M → N in D, postcomposition
gives Map_G(U(Ω), M) → Map_G(U(Ω), N), h ↦ t ∘ h. -/
def fieldEquivariantFunctionsPost
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) :
    FieldEquivariantFunctions.{u, w} k Ω U M →+
      FieldEquivariantFunctions.{u, w} k Ω U N where
  toFun h := {
    toFun := fun z => DiscreteAbelianAction.homToAdd t (h z)
    map_smul' := fun g z => by
      rw [h.map_smul]
      exact DiscreteAbelianAction.homToAdd_equivariant t g (h z) }
  map_zero' := by ext z; exact (DiscreteAbelianAction.homToAdd t).map_zero
  map_add' h h' := by ext z; exact (DiscreteAbelianAction.homToAdd t).map_add _ _

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For a coefficient map t : M → N in D, the equivariant function
postcomposition operator has value h ↦ (z ↦ t(h(z))). -/
@[deprecated fieldEquivariantFunctionsPost (since := "2026-10-28"), nolint defsWithUnderscore]
alias fieldEquivariantFunctions_post := fieldEquivariantFunctionsPost

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, this abelian presheaf has value Map_G(U(Ω), M)
on U and restriction h ↦ h ∘ r_Ω along an étale map r.
The identity and composition laws are those of the geometric fiber functor. -/
def fieldEquivariantFunctionPresheaf
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (Spec (.of k)).Etaleᵒᵖ ⥤ AddCommGrpCat.{max u w} where
  obj U := AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U.unop M)
  map r := AddCommGrpCat.ofHom (fieldEquivariantFunctionsRestrict.{u, w} k Ω r.unop M)
  map_id U := by
    ext h z
    change h ((fieldGeometricPoint k Ω).fiber.map (𝟙 U.unop) z) = h z
    rw [CategoryTheory.Functor.map_id]
    rfl
  map_comp r s := by
    ext h z
    change h ((fieldGeometricPoint k Ω).fiber.map (s.unop ≫ r.unop) z) =
      h ((fieldGeometricPoint k Ω).fiber.map r.unop
        ((fieldGeometricPoint k Ω).fiber.map s.unop z))
    rw [CategoryTheory.Functor.map_comp]
    rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
A map t : M → N in D gives a natural transformation between
the two equivariant-function presheaves, with component h ↦ t ∘ h
on every étale object U. -/
def fieldEquivariantFunctionPresheafMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    fieldEquivariantFunctionPresheaf.{u, w} k Ω M ⟶
      fieldEquivariantFunctionPresheaf.{u, w} k Ω N where
  app U := AddCommGrpCat.ofHom (fieldEquivariantFunctionsPost.{u, w} k Ω t U.unop)
  naturality U V r := by ext h; rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, this is its G-action on the underlying abelian group
in AddCommGrpCat c, obtained by forgetting the discrete topology while
retaining the coefficient action. -/
abbrev fieldModuleAbAction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Action AddCommGrpCat.{max u w} Gal(Ω/k) :=
  ((forget₂ (TopModuleCat.{max u w} ℤ) (ModuleCat.{max u w} ℤ) ⋙
    forget₂ (ModuleCat.{max u w} ℤ) AddCommGrpCat.{max u w}).mapAction Gal(Ω/k)).obj M.obj.obj

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
S_M is the skyscraper sheaf at Spec Ω → Spec k with coefficient
group M. On U it consists of all functions from the common lifted
geometric fiber to M, before imposing equivariance. -/
abbrev fieldSkyscraper
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.obj
    ((fieldModuleAbAction.{u, w} k Ω M).V)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For g ∈ G, the natural endomorphism I_g of the point skyscraper
functor acts by reindexing sections: I_g(s)(z) = s(g • z).
It is the right-adjoint mate of the corresponding stalk point map. -/
def fieldSkyscraperIndexMap (g : Gal(Ω/k)) :
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor
      (A := AddCommGrpCat.{max u w}) ⟶
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor :=
  conjugateEquiv
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafAdjunction
    (fieldGaloisPointEndomorphism.{u, w} k Ω g).sheafFiber

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The diagonal sheaf endomorphism is
D_g(s)(z) = g • s(g⁻¹ • z).
It reindexes by g⁻¹ and then applies the coefficient action of g. -/
def fieldSkyscraperDiagonalMap
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k)) :
    fieldSkyscraper.{u, w} k Ω M ⟶ fieldSkyscraper.{u, w} k Ω M :=
  (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app
      ((fieldModuleAbAction.{u, w} k Ω M).V) ≫
    (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
For g ∈ G and a common geometric coordinate z over U,
evaluation after D_g is the coordinate formula
(D_g s)(z) = g • s(g⁻¹ • z). -/
theorem fieldSkyscraperDiagonalMap_π
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k))
    (U : (Spec (.of k)).Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U) :
    (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) ≫
        Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber.obj U =>
            (fieldModuleAbAction.{u, w} k Ω M).V) z =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber.obj U =>
            (fieldModuleAbAction.{u, w} k Ω M).V)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U z) ≫
          ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom := by
  have hmap (Φ : (Spec (.of k)).smallEtaleTopology.Point.{max u w})
      {A B : AddCommGrpCat.{max u w}} (t : A ⟶ B)
      (V : (Spec (.of k)).Etale) (y : Φ.fiber.obj V) :
      (Φ.skyscraperSheafFunctor.map t).hom.app (op V) ≫ Pi.π (fun _ : Φ.fiber.obj V => B) y =
        Pi.π (fun _ : Φ.fiber.obj V => A) y ≫ t := by
    exact Pi.map_π (fun _ => t) y
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let C := (fieldModuleAbAction.{u, w} k Ω M).V
  let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
  let B := (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C
  have hm := hmap Φ a U z
  have hb : B.hom.app (op U) ≫ Pi.π (fun _ : Φ.fiber.obj U => C) z =
      Pi.π (fun _ : Φ.fiber.obj U => C)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U z) :=
    GrothendieckTopology.Point.conjugateEquiv_sheafFiber_app_π
      (fieldGaloisPointEndomorphism.{u, w} k Ω g⁻¹) C U z
  change B.hom.app (op U) ≫ ((Φ.skyscraperSheafFunctor.map a).hom.app (op U) ≫
    Pi.π (fun _ : Φ.fiber.obj U => C) z) = _
  exact (congrArg (fun t => B.hom.app (op U) ≫ t) hm).trans
    ((Category.assoc _ _ a).symm.trans (congrArg (fun t => t ≫ a) hb))


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The skyscraper index endomorphism for 1 ∈ G is the identity:
I₁ = id on the point skyscraper functor. -/
theorem fieldSkyscraperIndexMap_one :
    fieldSkyscraperIndexMap.{u, w} k Ω (1 : Gal(Ω/k)) = 𝟙 _ := by
  change conjugateEquiv _ _ (fieldGaloisStalkMap.{u, w} k Ω 1) = _
  rw [fieldGaloisStalkMap_one]
  exact conjugateEquiv_id _

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The reindexing endomorphisms satisfy I_(gh) = I_h ∘ I_g.
This is the composition order for precomposition by the G-action
on geometric coordinates. -/
theorem fieldSkyscraperIndexMap_mul (g h : Gal(Ω/k)) :
    fieldSkyscraperIndexMap.{u, w} k Ω (g * h) =
      fieldSkyscraperIndexMap.{u, w} k Ω g ≫ fieldSkyscraperIndexMap.{u, w} k Ω h := by
  change conjugateEquiv _ _ (fieldGaloisStalkMap.{u, w} k Ω (g * h)) = _
  rw [fieldGaloisStalkMap_mul]
  exact (conjugateEquiv_comp _ _ _ _ _).symm

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The diagonal endomorphism D₁ is the identity on S_M. -/
theorem fieldSkyscraperDiagonalMap_one
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    fieldSkyscraperDiagonalMap.{u, w} k Ω M 1 = 𝟙 _ := by
  change (fieldSkyscraperIndexMap.{u, w} k Ω (1 : Gal(Ω/k))⁻¹).app _ ≫ _ = _
  rw [inv_one, fieldSkyscraperIndexMap_one]
  simp only [NatTrans.id_app, Category.id_comp, map_one, End.one_asHom,
    CategoryTheory.Functor.map_id]

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The diagonal endomorphisms satisfy D_(gh) = D_g ∘ D_h.
This is the left G-action law on the skyscraper sheaf. -/
theorem fieldSkyscraperDiagonalMap_mul
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g h : Gal(Ω/k)) :
    fieldSkyscraperDiagonalMap.{u, w} k Ω M (g * h) =
      fieldSkyscraperDiagonalMap.{u, w} k Ω M h ≫
        fieldSkyscraperDiagonalMap.{u, w} k Ω M g := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let C := (fieldModuleAbAction.{u, w} k Ω M).V
  let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
  let b := ((fieldModuleAbAction.{u, w} k Ω M).ρ h).asHom
  have hab : ((fieldModuleAbAction.{u, w} k Ω M).ρ (g * h)).asHom = b ≫ a := by
    rw [map_mul, End.mul_asHom]
  change (fieldSkyscraperIndexMap.{u, w} k Ω (g * h)⁻¹).app C ≫
      Φ.skyscraperSheafFunctor.map _ = _
  rw [mul_inv_rev, fieldSkyscraperIndexMap_mul, NatTrans.comp_app, hab,
    CategoryTheory.Functor.map_comp]
  have hn := (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).naturality b
  change Φ.skyscraperSheafFunctor.map b ≫
      (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C =
    (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
      Φ.skyscraperSheafFunctor.map b at hn
  change _ = ((fieldSkyscraperIndexMap.{u, w} k Ω h⁻¹).app C ≫
    Φ.skyscraperSheafFunctor.map b) ≫
      ((fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
        Φ.skyscraperSheafFunctor.map a)
  simp only [Category.assoc]
  have hna : (fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
      (Φ.skyscraperSheafFunctor.map b ≫ Φ.skyscraperSheafFunctor.map a) =
    Φ.skyscraperSheafFunctor.map b ≫
      ((fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹).app C ≫
        Φ.skyscraperSheafFunctor.map a) :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun t => t ≫ Φ.skyscraperSheafFunctor.map a) hn.symm).trans
        (Category.assoc _ _ _))
  exact congrArg (fun t => (fieldSkyscraperIndexMap.{u, w} k Ω h⁻¹).app C ≫ t) hna

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The sheaf S_M with endomorphisms D_g forms a G-action object
in the category of abelian étale sheaves on Spec k. -/
def fieldSkyscraperDiagonalAction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Action (Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) Gal(Ω/k) where
  V := fieldSkyscraper.{u, w} k Ω M
  ρ := {
    toFun := fun g => End.of (fieldSkyscraperDiagonalMap.{u, w} k Ω M g)
    map_one' := by
      apply End.ext
      exact fieldSkyscraperDiagonalMap_one.{u, w} k Ω M
    map_mul' := fun g h => by
      apply End.ext
      exact fieldSkyscraperDiagonalMap_mul.{u, w} k Ω M g h }

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The single-object G-diagram of S_M and the maps D_g is the
invariant-skyscraper diagram. Its limit consists of sections fixed
by every diagonal endomorphism. -/
abbrev fieldSkyscraperInvariantDiagram
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    SingleObj Gal(Ω/k) ⥤ Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  SingleObj.functor (fieldSkyscraperDiagonalAction.{u, w} k Ω M).ρ

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D and z ∈ U(Ω), evaluation h ↦ h(z) is an additive
map Map_G(U(Ω), M) → M. -/
def fieldEquivariantFunctionEvaluation
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    FieldEquivariantFunctions.{u, w} k Ω U M →+
      (fieldModuleAbAction.{u, w} k Ω M).V where
  toFun h := h z
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The inclusion Φ̃_M → S_M sends h on U to the function on lifted
coordinates z ↦ h(z.down). It is natural under étale restrictions. -/
def fieldEquivariantFunctionInclusion
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    fieldEquivariantFunctionPresheaf.{u, w} k Ω M ⟶
      (fieldSkyscraper.{u, w} k Ω M).obj where
  app U := Pi.lift (fun z => AddCommGrpCat.ofHom
    (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop z.down))
  naturality U V r := by
    apply Pi.hom_ext
    intro z
    let P := fieldEquivariantFunctionPresheaf.{u, w} k Ω M
    let K := (fieldSkyscraper.{u, w} k Ω M).obj
    let C := (fieldModuleAbAction.{u, w} k Ω M).V
    let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let iU := Pi.lift (fun y : Φ.fiber.obj U.unop => AddCommGrpCat.ofHom
      (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop y.down))
    let iV := Pi.lift (fun y : Φ.fiber.obj V.unop => AddCommGrpCat.ofHom
      (fieldEquivariantFunctionEvaluation.{u, w} k Ω M V.unop y.down))
    have hV : iV ≫ Pi.π (fun _ : Φ.fiber.obj V.unop => C) z =
        AddCommGrpCat.ofHom
          (fieldEquivariantFunctionEvaluation.{u, w} k Ω M V.unop z.down) :=
      Pi.lift_comp_π _ _
    have hr : K.map r ≫ Pi.π (fun _ : Φ.fiber.obj V.unop => C) z =
        Pi.π (fun _ : Φ.fiber.obj U.unop => C) (Φ.fiber.map r.unop z) :=
      GrothendieckTopology.Point.skyscraperSheaf_restrict_π Φ C r.unop z
    have hU : iU ≫ Pi.π (fun _ : Φ.fiber.obj U.unop => C)
          (Φ.fiber.map r.unop z) = AddCommGrpCat.ofHom
        (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop
          (Φ.fiber.map r.unop z).down) := Pi.lift_comp_π _ _
    have hleft := (Category.assoc (P.map r) iV _).trans
      (congrArg (fun t => P.map r ≫ t) hV)
    have hright := (Category.assoc iU (K.map r) _).trans
      ((congrArg (fun t => iU ≫ t) hr).trans hU)
    exact hleft.trans hright.symm

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
At a common lifted coordinate z over U, the inclusion followed by
the product projection is evaluation h ↦ h(z.down). -/
@[reassoc]
theorem fieldEquivariantFunctionInclusion_π
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale)
    (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U) :
    (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app (op U) ≫
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V) z =
      AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U z.down) :=
  Pi.lift_comp_π _ _


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The inclusion i_M : Φ̃_M → S_M is invariant under each diagonal
action: D_g ∘ i_M = i_M for g ∈ G. -/
theorem fieldEquivariantFunctionInclusion_invariant
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k)) :
    fieldEquivariantFunctionInclusion.{u, w} k Ω M ≫
      (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom =
        fieldEquivariantFunctionInclusion.{u, w} k Ω M := by
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro z
  have hd := fieldSkyscraperDiagonalMap_π.{u, w} k Ω M g U.unop z
  have hi := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U.unop
    ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U.unop z)
  have hdiag := (Category.assoc _ _ _).trans
    ((congrArg (fun t => (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app U ≫ t)
      hd).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (fun t => t ≫ ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom) hi)))
  have hival := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U.unop z
  have hvalue : AddCommGrpCat.ofHom
      (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U.unop z).down) ≫
      ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom =
    AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U.unop z.down) := by
    ext h
    have hh := congrArg (fun a : DiscreteAbelianAction.underlying M => g • a)
      (h.map_smul g⁻¹ (show (fieldGeometricPoint k Ω).fiber.obj U.unop from z.down))
    exact hh.trans (smul_inv_smul g (h z.down))
  exact hdiag.trans (hvalue.trans hival.symm)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
For a section s ∈ S_M(U) satisfying D_g(s) = s for every g,
the function z ↦ s(ULift.up(z)) lies in Map_G(U(Ω), M).
Its equivariance follows from the diagonal fixed-section condition. -/
def fieldEquivariantFunctionOfInvariantSection
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale)
    (q : (fieldSkyscraper.{u, w} k Ω M).obj.obj (op U))
    (hq : ∀ g : Gal(Ω/k), (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) q = q) :
    FieldEquivariantFunctions.{u, w} k Ω U M where
  toFun z := Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
    (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
      (ULift.up z) q
  map_smul' g z := by
    let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
    let C := (fieldModuleAbAction.{u, w} k Ω M).V
    let : DistribMulAction Gal(Ω/k) C := DiscreteAbelianAction.instDistribMulAction M
    let y : Φ.fiber.obj U := ULift.up (g • z)
    have hfixed := congrArg (fun a => Pi.π (fun _ : Φ.fiber.obj U => C) y a) (hq g)
    have hcoord := congrArg (fun a => a q)
      (fieldSkyscraperDiagonalMap_π.{u, w} k Ω M g U y)
    change Pi.π (fun _ : Φ.fiber.obj U => C) y
        ((fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) q) =
      g • Pi.π (fun _ : Φ.fiber.obj U => C)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U y) q at hcoord
    have hy : (fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U y = ULift.up z := by
      apply ULift.ext
      change g⁻¹ • (g • z) = z
      exact inv_smul_smul g z
    exact hfixed.symm.trans (hcoord.trans
      (congrArg (fun a => g • Pi.π (fun _ : Φ.fiber.obj U => C) a q) hy))


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The presheaf Φ̃_M with inclusion i_M is a cone over the
invariant-skyscraper diagram after forgetting to presheaves.
Each cone leg is the same inclusion and is fixed by D_g. -/
def fieldInvariantFunctionCone
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Cone (fieldSkyscraperInvariantDiagram.{u, w} k Ω M ⋙
      sheafToPresheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) where
  pt := fieldEquivariantFunctionPresheaf.{u, w} k Ω M
  π := {
    app := fun _ => fieldEquivariantFunctionInclusion.{u, w} k Ω M
    naturality := fun _ _ g => by
      change fieldEquivariantFunctionInclusion.{u, w} k Ω M =
        fieldEquivariantFunctionInclusion.{u, w} k Ω M ≫
          (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom
      exact (fieldEquivariantFunctionInclusion_invariant.{u, w} k Ω M g).symm }

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
For a cone A over the invariant-skyscraper diagram evaluated at U,
the additive map A → Map_G(U(Ω), M) sends a to
z ↦ π_A(a)(ULift.up(z)), where π_A is its section component.
The cone equations make this function equivariant. -/
def fieldInvariantFunctionConeLift
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
    (c : Cone ((fieldSkyscraperInvariantDiagram.{u, w} k Ω M ⋙
      sheafToPresheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) ⋙
        (CategoryTheory.evaluation (Spec (.of k)).Etaleᵒᵖ AddCommGrpCat.{max u w}).obj (op U))) :
    c.pt ⟶ AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M) :=
  AddCommGrpCat.ofHom {
    toFun := fun x => fieldEquivariantFunctionOfInvariantSection.{u, w} k Ω M U
      (c.π.app (SingleObj.star Gal(Ω/k)) x) (fun g => by
        have hw := c.w (j := SingleObj.star Gal(Ω/k)) (j' := SingleObj.star Gal(Ω/k)) g
        change c.π.app (SingleObj.star Gal(Ω/k)) ≫
            (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) =
          c.π.app (SingleObj.star Gal(Ω/k)) at hw
        exact congrArg (fun a => a x) hw)
    map_zero' := by
      ext z
      exact ((Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
          (ULift.up z)).hom.comp (c.π.app (SingleObj.star Gal(Ω/k))).hom).map_zero
    map_add' := fun x y => by
      ext z
      exact ((Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
          (ULift.up z)).hom.comp (c.π.app (SingleObj.star Gal(Ω/k))).hom).map_add x y }

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
At every étale object U, the equivariant-function cone is a
limit of the evaluated diagonal G-action diagram.
Thus Map_G(U(Ω), M) is the fixed subgroup of S_M(U). -/
def fieldInvariantFunctionPointwiseLimit
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale) :
    IsLimit (((CategoryTheory.evaluation (Spec (.of k)).Etaleᵒᵖ AddCommGrpCat.{max u w}).obj
      (op U)).mapCone (fieldInvariantFunctionCone.{u, w} k Ω M)) where
  lift c := fieldInvariantFunctionConeLift.{u, w} k Ω M U c
  fac c j := by
    cases j
    apply Pi.hom_ext
    intro z
    have hi := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U z
    have hc := (Category.assoc (fieldInvariantFunctionConeLift.{u, w} k Ω M U c) _ _).trans
      (congrArg (fun a => fieldInvariantFunctionConeLift.{u, w} k Ω M U c ≫ a) hi)
    refine hc.trans ?_
    ext x
    change Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
        (ULift.up z.down) (c.π.app (SingleObj.star Gal(Ω/k)) x) =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
          z (c.π.app (SingleObj.star Gal(Ω/k)) x)
    cases z
    rfl
  uniq c m hm := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    apply MulActionHom.ext
    intro z
    have hh := congrArg (fun a => (a ≫ Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
      (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
        (ULift.up z)) x) (hm (SingleObj.star Gal(Ω/k)))
    have hi := congrArg (fun a => a (m x))
      (fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U (ULift.up z))
    exact hi.symm.trans hh

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The presheaf U ↦ Map_G(U(Ω), M) satisfies the sheaf condition
for the small étale topology on Spec k.
It is the presheaf of invariant sections of the point skyscraper. -/
theorem fieldEquivariantFunctionPresheaf_isSheaf
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Presheaf.IsSheaf (Spec (.of k)).smallEtaleTopology
      (fieldEquivariantFunctionPresheaf.{u, w} k Ω M) :=
  Sheaf.isSheaf_of_isLimit (fieldSkyscraperInvariantDiagram.{u, w} k Ω M)
    (fieldInvariantFunctionCone.{u, w} k Ω M)
      (evaluationJointlyReflectsLimits _ (fun U =>
        fieldInvariantFunctionPointwiseLimit.{u, w} k Ω M U.unop))


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The invariant-skyscraper sheaf Φ(M) is the sheaf with underlying
presheaf Φ̃_M. Its sections and restrictions are equivariant functions
and geometric-fiber precomposition. -/
def fieldInvariantSkyscraperInverseSheafObj
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} :=
  ⟨fieldEquivariantFunctionPresheaf.{u, w} k Ω M,
    fieldEquivariantFunctionPresheaf_isSheaf.{u, w} k Ω M⟩

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The functor Φ : D → Sheaf((Spec k)_ét, AddCommGrpCat c) sends
M to its invariant-skyscraper sheaf and a coefficient map t to
postcomposition h ↦ t ∘ h. -/
def fieldInvariantSkyscraperInverseSheaf :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤
      Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} where
  obj M := fieldInvariantSkyscraperInverseSheafObj.{u, w} k Ω M
  map t := ⟨fieldEquivariantFunctionPresheafMap.{u, w} k Ω t⟩
  map_id M := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext h
    rfl
  map_comp t t' := by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    ext h
    rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The sheaf Φ(M), with its inclusion into S_M, is a cone over
the single-object diagonal G-action diagram. -/
def fieldInvariantSkyscraperSheafCone
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Cone (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) where
  pt := fieldInvariantSkyscraperInverseSheafObj.{u, w} k Ω M
  π := {
    app := fun _ => ⟨fieldEquivariantFunctionInclusion.{u, w} k Ω M⟩
    naturality := fun _ _ g => by
      apply Sheaf.hom_ext
      exact (fieldEquivariantFunctionInclusion_invariant.{u, w} k Ω M g).symm }

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
The sheaf cone with vertex Φ(M) and leg i_M : Φ(M) → S_M
is limiting. It realizes the G-invariant part of the point skyscraper
inside the sheaf category. -/
def fieldInvariantSkyscraperSheafIsLimit
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    IsLimit (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M) :=
  isLimitOfReflects
    (sheafToPresheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (show IsLimit (fieldInvariantFunctionCone.{u, w} k Ω M) from
      evaluationJointlyReflectsLimits _ (fun U =>
        fieldInvariantFunctionPointwiseLimit.{u, w} k Ω M U.unop))

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
There is a canonical isomorphism α_M : lim_G S_M ≅ Φ(M)
between the action-diagram limit and the equivariant-function sheaf. -/
def fieldInvariantSkyscraperLimitIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    limit (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) ≅
      fieldInvariantSkyscraperInverseSheafObj.{u, w} k Ω M :=
  limit.isoLimitCone ⟨fieldInvariantSkyscraperSheafCone.{u, w} k Ω M,
    fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M⟩


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
For α_M : lim_G S_M ≅ Φ(M), the inclusion i_M and limit
projection π_lim satisfy i_M ∘ α_M = π_lim. -/
@[reassoc]
theorem fieldInvariantSkyscraperLimitIso_hom_inclusion
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) =
        limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k)) :=
  limit.isoLimitCone_hom_π _ _

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, let S_M be the point skyscraper of its underlying group,
with sections M^(ULift U(Ω)), and Φ̃_M(U) = Map_G(U(Ω), M).
For α_M : lim_G S_M ≅ Φ(M), one has
π_lim ∘ α_M⁻¹ = i_M as maps Φ(M) → S_M. -/
@[reassoc]
theorem fieldInvariantSkyscraperLimitIso_inv_π
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).inv ≫
      limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k)) =
        (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) :=
  limit.isoLimitCone_inv_π _ _


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For any commutative k-algebra A in universe u, its algebra maps
A →ₐ[k] Ω carry the G-action g • ξ = g ∘ ξ.
No finite étale condition on A is needed for this action. -/
instance fieldAlgebraEmbeddingMulAction (A : Type u) [CommRing A] [Algebra k A] :
    MulAction Gal(Ω/k) (A →ₐ[k] Ω) where
  smul g ξ := g.toAlgHom.comp ξ
  one_smul ξ := by ext a; rfl
  mul_smul g h ξ := by ext a; rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For a finite étale k-algebra A, the geometric-fiber comparison
(Spec A)(Ω) → Hom_(k-alg)(A, Ω) is G-equivariant, with postcomposition
by G on algebra embeddings. -/
def fieldFiniteEtaleFiberEquivariant (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A) →[Gal(Ω/k)]
      (A.unop →ₐ[k] Ω) where
  toFun := (fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A
  map_smul' g z := by
    exact fieldGaloisSpec_homEquivAlgHom k Ω g z.left z.w

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For a finite étale k-algebra A, the inverse algebra-embedding
comparison Hom_(k-alg)(A, Ω) → (Spec A)(Ω) is also G-equivariant. -/
def fieldFiniteEtaleFiberEquivariantInv (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    (A.unop →ₐ[k] Ω) →[Gal(Ω/k)]
      (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A) :=
  MulActionHom.inverse (fieldFiniteEtaleFiberEquivariant k Ω A)
    ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A)
    (fieldFiniteEtaleFiberEquiv k Ω A).symm_apply_apply
    (fieldFiniteEtaleFiberEquiv k Ω A).apply_symm_apply

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D and finite étale k-algebra A, this additive equivalence
identifies Φ(M)(Spec A) with
Map_G(Hom_(k-alg)(A, Ω), M). -/
def fieldInvariantFiniteEtaleSectionsEquiv
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A)) ≃+
        ((A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) where
  toFun h := h.comp (fieldFiniteEtaleFiberEquivariantInv k Ω A)
  invFun h := h.comp (fieldFiniteEtaleFiberEquivariant k Ω A)
  left_inv h := by
    apply MulActionHom.ext
    intro z
    let h0 : FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M := h
    exact congrArg h0 ((fieldFiniteEtaleFiberEquiv k Ω A).symm_apply_apply z)
  right_inv h := by
    apply MulActionHom.ext
    intro ξ
    exact congrArg h ((fieldFiniteEtaleFiberEquiv k Ω A).apply_symm_apply ξ)
  map_add' h h' := by ext ξ; rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For finite étale A, let e_A : (Spec A)(Ω) ≅ Hom_(k-alg)(A, Ω).
The section equivalence sends h to ξ ↦ h(e_A⁻¹(ξ)). -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω) :
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ =
      (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from h)
        ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A ξ) := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For a finite étale algebra map b : B → A and a section h over
Spec B, the finite-value equivalences identify restriction to Spec A
with ξ ↦ h(ξ ∘ b), for ξ : A →ₐ[k] Ω. -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (r : A ⟶ B)
    (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj B))) (ξ : A.unop →ₐ[k] Ω) :
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
          ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
      fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom) := by
  let h0 : FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj B) M := h
  change h0 ((fieldGeometricPoint k Ω).fiber.map ((fieldFiniteEtaleToEtale k).map r)
      ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A ξ)) =
    h0 ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app B (ξ.comp r.unop.hom.hom))
  apply congrArg h0
  apply (fieldFiniteEtaleFiberEquiv k Ω B).injective
  have hn := fieldFiniteEtaleFiberEquiv_naturality k Ω r
    ((fieldFiniteEtaleFiberEquiv k Ω A).symm ξ)
  exact hn.trans ((congrArg (fun a => a.comp r.unop.hom.hom)
    ((fieldFiniteEtaleFiberEquiv k Ω A).apply_symm_apply ξ)).trans
      ((fieldFiniteEtaleFiberEquiv k Ω B).apply_symm_apply (ξ.comp r.unop.hom.hom)).symm)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For t : M → N in D and finite étale A, the finite-value
equivalences identify Φ(t)_A with pointwise postcomposition:
h(ξ) ↦ t(h(ξ)). -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω) :
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω N A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
          (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
      DiscreteAbelianAction.homToAdd t
        (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ) :=
  rfl


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
A map t : M → N in D gives the same equivariant additive morphism
between the underlying abelian-group G-action objects. -/
def fieldModuleAbActionMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    fieldModuleAbAction.{u, w} k Ω M ⟶ fieldModuleAbAction.{u, w} k Ω N :=
  ((forget₂ (TopModuleCat.{max u w} ℤ) (ModuleCat.{max u w} ℤ) ⋙
    forget₂ (ModuleCat.{max u w} ℤ) AddCommGrpCat.{max u w}).mapAction Gal(Ω/k)).map t.hom.hom

omit [IsSepClosure k Ω] in
/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For t : M → N in D, the underlying map of its abelian-group
action morphism equals the map U(t) given by forgetting the topology
and G-action. -/
theorem fieldModuleAbActionMap_hom
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    (fieldModuleAbActionMap.{u, w} k Ω t).hom =
      (DiscreteAbelianAction.forget Gal(Ω/k)).map t := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For t : M → N in D and g ∈ G, the skyscraper map S(t) obeys
S(t) ∘ D_g^M = D_g^N ∘ S(t).
Thus the diagonal action is natural in equivariant coefficients. -/
theorem fieldSkyscraperDiagonalMap_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) (g : Gal(Ω/k)) :
    fieldSkyscraperDiagonalMap.{u, w} k Ω M g ≫
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom ≫
      fieldSkyscraperDiagonalMap.{u, w} k Ω N g := by
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let I := fieldSkyscraperIndexMap.{u, w} k Ω g⁻¹
  let CM := (fieldModuleAbAction.{u, w} k Ω M).V
  let CN := (fieldModuleAbAction.{u, w} k Ω N).V
  let a := ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom
  let b := ((fieldModuleAbAction.{u, w} k Ω N).ρ g).asHom
  let f := (fieldModuleAbActionMap.{u, w} k Ω t).hom
  have hc : a ≫ f = f ≫ b := (fieldModuleAbActionMap.{u, w} k Ω t).comm g
  have hn : Φ.skyscraperSheafFunctor.map f ≫ I.app CN =
      I.app CM ≫ Φ.skyscraperSheafFunctor.map f := I.naturality f
  change (I.app CM ≫ Φ.skyscraperSheafFunctor.map a) ≫ Φ.skyscraperSheafFunctor.map f =
    Φ.skyscraperSheafFunctor.map f ≫ (I.app CN ≫ Φ.skyscraperSheafFunctor.map b)
  calc
    _ = I.app CM ≫ Φ.skyscraperSheafFunctor.map (a ≫ f) :=
      (Category.assoc _ _ _).trans (congrArg (fun q => I.app CM ≫ q)
        (Φ.skyscraperSheafFunctor.map_comp a f).symm)
    _ = I.app CM ≫ Φ.skyscraperSheafFunctor.map (f ≫ b) :=
      congrArg (fun q => I.app CM ≫ Φ.skyscraperSheafFunctor.map q) hc
    _ = I.app CM ≫ (Φ.skyscraperSheafFunctor.map f ≫ Φ.skyscraperSheafFunctor.map b) :=
      congrArg (fun q => I.app CM ≫ q) (Φ.skyscraperSheafFunctor.map_comp f b)
    _ = (I.app CM ≫ Φ.skyscraperSheafFunctor.map f) ≫ Φ.skyscraperSheafFunctor.map b :=
      (Category.assoc _ _ _).symm
    _ = (Φ.skyscraperSheafFunctor.map f ≫ I.app CN) ≫ Φ.skyscraperSheafFunctor.map b :=
      congrArg (fun q => q ≫ Φ.skyscraperSheafFunctor.map b) hn.symm
    _ = _ := Category.assoc _ _ _

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For t : M → N in D, the map of invariant-skyscraper G-diagrams
has sole component S(t), commuting with every diagonal endomorphism. -/
def fieldSkyscraperInvariantDiagramMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    fieldSkyscraperInvariantDiagram.{u, w} k Ω M ⟶
      fieldSkyscraperInvariantDiagram.{u, w} k Ω N :=
  SingleObj.natTrans
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
      (fieldModuleAbActionMap.{u, w} k Ω t).hom)
    (fieldSkyscraperDiagonalMap_naturality.{u, w} k Ω t)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The invariant-skyscraper diagrams form a functor from D to the
category of G-shaped diagrams of abelian étale sheaves, with coefficient
maps acting by the skyscraper maps S(t). -/
def fieldSkyscraperInvariantDiagrams :
    DiscreteAbelianAction.{u, max u w} Gal(Ω/k) ⥤
      SingleObj Gal(Ω/k) ⥤
        Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} where
  obj M := fieldSkyscraperInvariantDiagram.{u, w} k Ω M
  map t := fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t
  map_id M := by
    apply NatTrans.ext
    funext j
    exact (congrArg
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
      ((DiscreteAbelianAction.forget Gal(Ω/k)).map_id M)).trans
      ((smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map_id _)
  map_comp t t' := by
    apply NatTrans.ext
    funext j
    exact (congrArg
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
      ((DiscreteAbelianAction.forget Gal(Ω/k)).map_comp t t')).trans
      ((smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map_comp _ _)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For t : M → N in D, the invariant inclusions satisfy
i_N ∘ Φ(t) = S(t) ∘ i_M.
Postcomposition of equivariant functions commutes with inclusion. -/
theorem fieldInvariantSkyscraperInclusion_naturality
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) :
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω N).π.app (SingleObj.star Gal(Ω/k)) =
    (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) ≫
      (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t).app (SingleObj.star Gal(Ω/k)) := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply Pi.hom_ext
  intro z
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  let CM := (fieldModuleAbAction.{u, w} k Ω M).V
  let CN := (fieldModuleAbAction.{u, w} k Ω N).V
  let f := (fieldModuleAbActionMap.{u, w} k Ω t).hom
  let iM := (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app U
  let iN := (fieldEquivariantFunctionInclusion.{u, w} k Ω N).app U
  let a := ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app U
  have hN := fieldEquivariantFunctionInclusion_π.{u, w} k Ω N U.unop z
  have hmap : (Φ.skyscraperSheafFunctor.map f).hom.app U ≫
      Pi.π (fun _ : Φ.fiber.obj U.unop => CN) z =
    Pi.π (fun _ : Φ.fiber.obj U.unop => CM) z ≫ f := Pi.map_π (fun _ => f) z
  have hM := fieldEquivariantFunctionInclusion_π.{u, w} k Ω M U.unop z
  have hleft := (Category.assoc a iN _).trans (congrArg (fun q => a ≫ q) hN)
  have hright := (Category.assoc iM _ _).trans
    ((congrArg (fun q => iM ≫ q) hmap).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (fun q => q ≫ f) hM)))
  refine hleft.trans (Eq.trans ?_ hright.symm)
  ext h
  rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The comparison α_M : lim_G S_M ≅ Φ(M) is natural in M.
For t : M → N, α_N ∘ lim(S(t)) = Φ(t) ∘ α_M,
giving the natural isomorphism between the limit-diagram functor and Φ. -/
def fieldInvariantSkyscraperLimitNatIso :
    fieldSkyscraperInvariantDiagrams.{u, w} k Ω ⋙ lim ≅
      fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω :=
  NatIso.ofComponents (fieldInvariantSkyscraperLimitIso.{u, w} k Ω) (fun {M N} t => by
    apply (fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω N).hom_ext
    intro j
    cases j
    have hN := fieldInvariantSkyscraperLimitIso_hom_inclusion.{u, w} k Ω N
    have hM := fieldInvariantSkyscraperLimitIso_hom_inclusion.{u, w} k Ω M
    have hi := fieldInvariantSkyscraperInclusion_naturality.{u, w} k Ω t
    have hl := (Category.assoc _ _ _).trans
      ((congrArg (fun q => limMap (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t) ≫ q)
        hN).trans (limMap_π (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t)
          (SingleObj.star Gal(Ω/k))))
    have hr := (Category.assoc _ _ _).trans
      ((congrArg (fun q => (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫ q)
        hi).trans ((Category.assoc _ _ _).symm.trans
          (congrArg (fun q => q ≫
            (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t).app (SingleObj.star Gal(Ω/k))) hM)))
    exact hl.trans hr.symm)


/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D and U ∈ Etale(Spec k), the group Φ(M)(U) is
Map_G(U(Ω), M), with pointwise abelian-group operations. -/
theorem fieldInvariantSkyscraperInverseSheaf_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale) :
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj (op U) =
      AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M) := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For M ∈ D, r : V → U étale, and h ∈ Φ(M)(U), restriction
has value (h|_V)(z) = h(r_Ω(z)) for z ∈ V(Ω). -/
theorem fieldInvariantSkyscraperInverseSheaf_restrict_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {U V : (Spec (.of k)).Etale} (r : V ⟶ U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj V) :
    (show FieldEquivariantFunctions.{u, w} k Ω V M from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map r.op h) z =
        h ((fieldGeometricPoint k Ω).fiber.map r z) := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For t : M → N in D, h ∈ Φ(M)(U) and z ∈ U(Ω), the
coefficient sheaf map has value Φ(t)_U(h)(z) = t(h(z)). -/
theorem fieldInvariantSkyscraperInverseSheaf_map_apply
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (show FieldEquivariantFunctions.{u, w} k Ω U N from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app (op U) h) z =
        DiscreteAbelianAction.homToAdd t (h z) := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For finite étale A and e_A : (Spec A)(Ω) ≅ Hom_(k-alg)(A, Ω),
the inverse finite-value equivalence sends an equivariant function h
on algebra embeddings to z ↦ h(e_A(z)) on geometric lifts. -/
theorem fieldInvariantFiniteEtaleSectionsEquiv_symm_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : (A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M)
    (z : (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A)) :
    (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from
      (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A).symm h) z =
        h ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A z) := rfl

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
This proposition records the limiting invariant sheaf cone,
D₁ = id and D_(gh) = D_g ∘ D_h, the coordinate formula
D_g(s)(z) = g • s(g⁻¹ • z), and the inclusion evaluation formula.
It also records the natural comparisons lim_G S_M ≅ Φ(M),
their forward/inverse projection identities, and naturality of
diagonal actions, inclusions and limits under every coefficient map. -/
def FieldInvariantSkyscraperLimitLaws : Prop :=
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    Nonempty (IsLimit (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M))) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    fieldSkyscraperDiagonalMap.{u, w} k Ω M 1 = 𝟙 _) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g h : Gal(Ω/k)),
    fieldSkyscraperDiagonalMap.{u, w} k Ω M (g * h) =
      fieldSkyscraperDiagonalMap.{u, w} k Ω M h ≫
        fieldSkyscraperDiagonalMap.{u, w} k Ω M g) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k))
      (U : (Spec (.of k)).Etale)
      (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U),
    (fieldSkyscraperDiagonalMap.{u, w} k Ω M g).hom.app (op U) ≫
        Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
          (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V) z =
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V)
        ((fieldGaloisCommonFiberMap.{u, w} k Ω g⁻¹).app U z) ≫
          ((fieldModuleAbAction.{u, w} k Ω M).ρ g).asHom) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).fiber.obj U),
    (fieldEquivariantFunctionInclusion.{u, w} k Ω M).app (op U) ≫
      Pi.π (fun _ : (smallEtaleGeometricPointCommon.{u, w}
        (Spec.algebraMap k Ω)).fiber.obj U => (fieldModuleAbAction.{u, w} k Ω M).V) z =
        AddCommGrpCat.ofHom (fieldEquivariantFunctionEvaluation.{u, w} k Ω M U z.down)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperLimitNatIso.{u, w} k Ω).app M =
      fieldInvariantSkyscraperLimitIso.{u, w} k Ω M) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) =
        limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k))) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).inv ≫
      limit.π (fieldSkyscraperInvariantDiagram.{u, w} k Ω M) (SingleObj.star Gal(Ω/k)) =
        (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k))) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) (g : Gal(Ω/k)),
    fieldSkyscraperDiagonalMap.{u, w} k Ω M g ≫
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).skyscraperSheafFunctor.map
        (fieldModuleAbActionMap.{u, w} k Ω t).hom ≫
      fieldSkyscraperDiagonalMap.{u, w} k Ω N g) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N),
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t ≫
      (fieldInvariantSkyscraperSheafCone.{u, w} k Ω N).π.app (SingleObj.star Gal(Ω/k)) =
    (fieldInvariantSkyscraperSheafCone.{u, w} k Ω M).π.app (SingleObj.star Gal(Ω/k)) ≫
      (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t).app (SingleObj.star Gal(Ω/k))) ∧
  ∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N),
    limMap (fieldSkyscraperInvariantDiagramMap.{u, w} k Ω t) ≫
      (fieldInvariantSkyscraperLimitIso.{u, w} k Ω N).hom =
    (fieldInvariantSkyscraperLimitIso.{u, w} k Ω M).hom ≫
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
This proposition records Φ(M)(U) = Map_G(U(Ω), M), restriction
h ↦ h ∘ r_Ω, coefficient maps h ↦ t ∘ h, and the identity and
composition laws of Φ. It includes the pointwise formulas for addition,
negation and zero on equivariant sections. -/
def FieldInvariantSkyscraperOriginalValuesLaws : Prop :=
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale),
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj (op U) =
      AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) {U V : (Spec (.of k)).Etale}
      (r : V ⟶ U) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj V),
    (show FieldEquivariantFunctions.{u, w} k Ω V M from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map r.op h) z =
        h ((fieldGeometricPoint k Ω).fiber.map r z)) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
      (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (show FieldEquivariantFunctions.{u, w} k Ω U N from
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app (op U) h) z =
        DiscreteAbelianAction.homToAdd t (h z)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map (𝟙 M) = 𝟙 _) ∧
  (∀ {M N P : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N) (t' : N ⟶ P),
    (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map (t ≫ t') =
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t ≫
        (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t') ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (h h' : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (h + h') z = h z + h' z) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (h : FieldEquivariantFunctions.{u, w} k Ω U M)
      (z : (fieldGeometricPoint k Ω).fiber.obj U), (-h) z = -(h z)) ∧
  ∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale)
      (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (0 : FieldEquivariantFunctions.{u, w} k Ω U M) z = 0

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
For every finite étale k-algebra A, this proposition records both
directions of Φ(M)(Spec A) ≅ Map_G(Hom_(k-alg)(A, Ω), M),
with values h(e_A⁻¹(ξ)) and h(e_A(z)).
It includes restriction by ξ ↦ ξ ∘ b, postcomposition by coefficient
maps, and G-equivariance of the fiber/algebra-embedding comparison. -/
def FieldInvariantSkyscraperFiniteValuesLaws : Prop :=
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω),
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ =
      (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from h)
        ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app A ξ)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (h : (A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M)
      (z : (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A)),
    (show FieldEquivariantFunctions.{u, w} k Ω ((fieldFiniteEtaleToEtale k).obj A) M from
      (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A).symm h) z =
        h ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A z)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
      {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (r : A ⟶ B)
      (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj B))) (ξ : A.unop →ₐ[k] Ω),
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
          ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
      fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom)) ∧
  (∀ {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
      (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
      (h : ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω),
    fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω N A
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
          (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
      DiscreteAbelianAction.homToAdd t
        (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A h ξ)) ∧
  ∀ (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (g : Gal(Ω/k))
      (z : (fieldGeometricPoint k Ω).fiber.obj ((fieldFiniteEtaleToEtale k).obj A)),
    (fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A (g • z) =
      g.toAlgHom.comp ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app A z)

/-- Let Ω/k be a separable closure of fields in universe u,
G = Gal(Ω/k), and c = max(u, w). Let D be the category of discrete
continuous G-modules with abelian-group carriers in universe c.
For an étale k-scheme U, write U(Ω) for its geometric lifts.
The invariant-skyscraper sheaf functor has all the stated limit,
action, section, functor and finite étale value properties.
The construction uses the chosen closure Ω, the common coefficient
universe c, and all étale objects without finiteness assumptions on M or G. -/
theorem original_field_invariant_skyscraper_inverse_sheaf :
    FieldInvariantSkyscraperLimitLaws.{u, w} k Ω ∧
      FieldInvariantSkyscraperOriginalValuesLaws.{u, w} k Ω ∧
        FieldInvariantSkyscraperFiniteValuesLaws.{u, w} k Ω := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨fun M => ⟨fieldInvariantSkyscraperSheafIsLimit.{u, w} k Ω M⟩,
      fieldSkyscraperDiagonalMap_one.{u, w} k Ω,
      fieldSkyscraperDiagonalMap_mul.{u, w} k Ω,
      fieldSkyscraperDiagonalMap_π.{u, w} k Ω,
      fieldEquivariantFunctionInclusion_π.{u, w} k Ω,
      fun _ => rfl,
      fieldInvariantSkyscraperLimitIso_hom_inclusion.{u, w} k Ω,
      fieldInvariantSkyscraperLimitIso_inv_π.{u, w} k Ω,
      fieldSkyscraperDiagonalMap_naturality.{u, w} k Ω,
      fieldInvariantSkyscraperInclusion_naturality.{u, w} k Ω, ?_⟩
    intro M N t
    exact (fieldInvariantSkyscraperLimitNatIso.{u, w} k Ω).hom.naturality t
  · exact ⟨fieldInvariantSkyscraperInverseSheaf_value.{u, w} k Ω,
      fieldInvariantSkyscraperInverseSheaf_restrict_apply.{u, w} k Ω,
      fieldInvariantSkyscraperInverseSheaf_map_apply.{u, w} k Ω,
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map_id,
      (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map_comp,
      fun _ _ _ _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ => rfl⟩
  · refine ⟨fieldInvariantFiniteEtaleSectionsEquiv_apply.{u, w} k Ω,
      fieldInvariantFiniteEtaleSectionsEquiv_symm_apply.{u, w} k Ω,
      fieldInvariantFiniteEtaleSectionsEquiv_restrict.{u, w} k Ω,
      fieldInvariantFiniteEtaleSectionsEquiv_map.{u, w} k Ω, ?_⟩
    intro A g z
    exact (fieldFiniteEtaleFiberEquivariant k Ω A).map_smul g z

end AlgebraicGeometry.Scheme.DerivedSections
