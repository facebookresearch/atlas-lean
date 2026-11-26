/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldEquivariantStalkCounitIsomorphism
public import MathlibExt.AlgebraicGeometry.Sites.FieldGeometricStalkConservativity
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-!
# Étale sheaves and discrete Galois modules over a field

Let Ω/k be a separable closure of fields in universe u and c = max(u, w).
The geometric-stalk functor E at Spec Ω → Spec k is an equivalence
between AddCommGrpCat c-valued sheaves on the small étale site of Spec k
and discrete abelian groups with continuous G = Gal(Ω/k)-action.

Its inverse Φ takes a module M to the sheaf U ↦ Map_G(U(Ω), M).
Restriction precomposes with the map on geometric lifts, while a module
morphism postcomposes the equivariant function. The unit sends a section a
to z ↦ germ_z(a), and the counit sends the germ of a function h at z
to h(z). These maps are natural isomorphisms satisfying both triangle
identities. On a finite étale k-algebra A the inverse value is
Map_G(Hom_(k-alg)(A, Ω), M). The same unit formula applies after lifting
coefficients from universe w to c.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For every coefficient sheaf Q, E(η_Q) = ε_(E(Q))⁻¹.
The stalk image of the unit is the inverse of the evaluation counit. -/
theorem fieldEquivariantStalkUnit_map_eq_counit_inv
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
        ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q) =
      inv ((fieldEquivariantStalkCounit.{u, w} k Ω).app
        ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)) := by
  let a := (fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
    ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q)
  let b := (fieldEquivariantStalkCounit.{u, w} k Ω).app
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q)
  have h : a ≫ b = 𝟙 _ := fieldEquivariantStalk_left_triangle.{u, w} k Ω Q
  calc
    a = a ≫ (b ≫ inv b) := (by rw [IsIso.hom_inv_id, Category.comp_id])
    _ = (a ≫ b) ≫ inv b := (Category.assoc _ _ _).symm
    _ = inv b := by rw [h, Category.id_comp]

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For every coefficient sheaf Q, the unit η_Q : Q → Φ(E(Q))
is an isomorphism of étale sheaves. -/
instance fieldEquivariantStalkUnit_isIso
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    IsIso ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q) := by
  let : IsIso ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).map
      ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q)) := by
    rw [fieldEquivariantStalkUnit_map_eq_counit_inv.{u, w} k Ω Q]
    infer_instance
  exact isIso_of_reflects_iso _ (fieldGeometricStalkGaloisFunctor.{u, w} k Ω)

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
These functors give the equivalence
Sheaf((Spec k)_ét, AddCommGrpCat c) ≌ D_G,
where D_G is the category of discrete continuous G-modules. -/
def fieldSheafGaloisEquivalence :
    Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w} ≌
      DiscreteAbelianAction.{u, max u w} Gal(Ω/k) :=
  (fieldEquivariantStalkAdjunction.{u, w} k Ω).toEquivalence

theorem fieldSheafGaloisEquivalence_functor :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).functor =
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω := rfl

theorem fieldSheafGaloisEquivalence_inverse :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).inverse =
      fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω := rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
The unit of the sheaf–Galois equivalence is η : id → Φ E,
the geometric-germ reconstruction map. -/
theorem fieldSheafGaloisEquivalence_unit_hom :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom =
      fieldEquivariantStalkUnit.{u, w} k Ω := rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
The counit of the sheaf–Galois equivalence is ε : E Φ → id,
the evaluation map on equivariant-function germs. -/
theorem fieldSheafGaloisEquivalence_counit_hom :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom =
      fieldEquivariantStalkCounit.{u, w} k Ω := rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For every coefficient sheaf Q, the triangle equation is
ε_(E(Q)) ∘ E(η_Q) = id_(E(Q)). -/
theorem fieldSheafGaloisEquivalence_left_triangle
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w}) :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).functor.map
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q) ≫
      (fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).functor.obj Q) = 𝟙 _ :=
  fieldEquivariantStalk_left_triangle.{u, w} k Ω Q

theorem fieldSheafGaloisEquivalence_right_triangle
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M) ≫
      (fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.map
        ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M) = 𝟙 _ :=
  fieldEquivariantStalk_right_triangle.{u, w} k Ω M

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For a coefficient sheaf Q, U ∈ Etale(Spec k), z ∈ U(Ω), and
a ∈ Q(U), the unit section has value
η_Q,U(a)(z) = germ_(U,z)(a). -/
theorem fieldSheafGaloisEquivalence_unit_germ
    (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).functor.obj Q) from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app Q).hom.app (op U) c) z =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) Q.obj c :=
  fieldEquivariantStalkUnit_germ.{u, w} k Ω Q U z c

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For M ∈ D_G and h ∈ Φ(M)(U), the counit evaluates a germ:
ε_M(germ_(U,z)(h)) = h(z). -/
theorem fieldSheafGaloisEquivalence_counit_germ
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M) :
    DiscreteAbelianAction.homToAdd
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).counitIso.hom.app M)
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj h) = h z :=
  fieldEquivariantStalkCounit_germ.{u, w} k Ω M U z h

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For every étale k-scheme U, the inverse sheaf value Φ(M)(U)
is the abelian group of G-equivariant functions U(Ω) → M,
with pointwise addition. -/
theorem fieldSheafGaloisEquivalence_inverse_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale) :
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj (op U) =
      AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M) := rfl

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For an étale map r : V → U and h : U(Ω) → M equivariant,
restriction in Φ(M) has value
(h|_V)(z) = h(r(z)) for z ∈ V(Ω). -/
theorem fieldSheafGaloisEquivalence_inverse_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {U V : (Spec (.of k)).Etale} (r : V ⟶ U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj V) :
    (show FieldEquivariantFunctions.{u, w} k Ω V M from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.map r.op h) z =
        h ((fieldGeometricPoint k Ω).fiber.map r z) :=
  fieldInvariantSkyscraperInverseSheaf_restrict_apply.{u, w} k Ω M r h z

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For an equivariant additive map t : M → N, the inverse sheaf
morphism Φ(t) sends an equivariant section h on U to t ∘ h.
Its value at z is t(h(z)). -/
theorem fieldSheafGaloisEquivalence_inverse_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj U) :
    (show FieldEquivariantFunctions.{u, w} k Ω U N from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.map t).hom.app (op U) h) z =
      DiscreteAbelianAction.homToAdd t (h z) :=
  fieldInvariantSkyscraperInverseSheaf_map_apply.{u, w} k Ω t U h z

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For a finite étale k-algebra A, this additive equivalence identifies
Φ(M)(Spec A) with Map_G(Hom_(k-alg)(A, Ω), M).
The group acts on algebra embeddings by postcomposition and on M
through its given continuous action. -/
@[nolint defsWithUnderscore]
def fieldSheafGaloisEquivalence_finite_value
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) :
    ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj
        (op ((fieldFiniteEtaleToEtale k).obj A)) ≃+
      ((A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) :=
  fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M A

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For a map b : B → A of finite étale k-algebras and an equivariant
section h on Spec B, restriction to Spec A has value
ξ ↦ h(ξ ∘ b) for ξ : A →ₐ[k] Ω, under the finite étale value
equivalences. -/
theorem fieldSheafGaloisEquivalence_finite_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ} (r : A ⟶ B)
    (h : ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj B))) (ξ : A.unop →ₐ[k] Ω) :
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A
        (((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.map
          ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
      fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom) :=
  fieldInvariantFiniteEtaleSectionsEquiv_restrict.{u, w} k Ω M r h ξ

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For a G-module morphism t : M → N and finite étale k-algebra A,
the finite étale value equivalences identify Φ(t)_A with
pointwise postcomposition h ↦ t ∘ h. -/
theorem fieldSheafGaloisEquivalence_finite_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : ((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.obj M).obj.obj
      (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω) :
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω N A
        (((fieldSheafGaloisEquivalence.{u, w} k Ω).inverse.map t).hom.app
          (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
      DiscreteAbelianAction.homToAdd t
        (fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A h ξ) :=
  fieldInvariantFiniteEtaleSectionsEquiv_map.{u, w} k Ω t A h ξ

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
For an étale sheaf F with coefficients in universe w, lift it
to c = max(u, w). The equivalence unit on a lifted section ULift.up(a)
over U has value at z equal to the germ of ULift.up(a) at the lifted
geometric coordinate z. -/
theorem fieldSheafGaloisEquivalence_original_unit_germ
    (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)) :
    (show FieldEquivariantFunctions.{u, w} k Ω U
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).functor.obj
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) from
      ((fieldSheafGaloisEquivalence.{u, w} k Ω).unitIso.hom.app
        ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app (op U) (ULift.up c)) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
      (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c) :=
  fieldEquivariantStalkUnit_original_germ.{u, w} k Ω F U z c

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
This proposition records the stalk and equivariant-function inverse
functors, their invertible unit and counit, both triangle identities
and their naturality. It includes the germ formulas η(a)(z) = germ_z(a)
and ε(germ_z(h)) = h(z), the inverse sheaf's restriction and coefficient
maps, the finite étale algebra value equivalences with their maps,
and the unit formula for coefficients lifted from w to c. -/
def OriginalFieldSheafGaloisEquivalenceLaws : Prop :=
  let E := fieldSheafGaloisEquivalence.{u, w} k Ω
  let T := fieldGeometricStalkGaloisFunctor.{u, w} k Ω
  let R := fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω
  E.functor = T ∧ E.inverse = R ∧
  E.unitIso.hom = fieldEquivariantStalkUnit.{u, w} k Ω ∧
  E.counitIso.hom = fieldEquivariantStalkCounit.{u, w} k Ω ∧
  (∀ Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w},
    IsIso ((fieldEquivariantStalkUnit.{u, w} k Ω).app Q)) ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    IsIso ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) ∧
  (∀ Q, T.map (E.unitIso.hom.app Q) ≫ E.counitIso.hom.app (T.obj Q) = 𝟙 _) ∧
  (∀ M, E.unitIso.hom.app (R.obj M) ≫ R.map (E.counitIso.hom.app M) = 𝟙 _) ∧
  (∀ (Q : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : Q.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U (T.obj Q) from
      (E.unitIso.hom.app Q).hom.app (op U) c) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      U (ULift.up z) Q.obj c) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M),
    DiscreteAbelianAction.homToAdd (E.counitIso.hom.app M)
      ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        U (ULift.up z) (R.obj M).obj h) = h z) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (U : (Spec (.of k)).Etale),
    (R.obj M).obj.obj (op U) = AddCommGrpCat.of (FieldEquivariantFunctions.{u, w} k Ω U M)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U V : (Spec (.of k)).Etale) (r : V ⟶ U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj V),
    (show FieldEquivariantFunctions.{u, w} k Ω V M from (R.obj M).obj.map r.op h) z =
      h ((fieldGeometricPoint k Ω).fiber.map r z)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N)
    (U : (Spec (.of k)).Etale) (h : FieldEquivariantFunctions.{u, w} k Ω U M)
    (z : (fieldGeometricPoint k Ω).fiber.obj U),
    (show FieldEquivariantFunctions.{u, w} k Ω U N from (R.map t).hom.app (op U) h) z =
      DiscreteAbelianAction.homToAdd t (h z)) ∧
  (∀ (Q Q' : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{max u w})
    (τ : Q ⟶ Q'), τ ≫ E.unitIso.hom.app Q' =
      E.unitIso.hom.app Q ≫ R.map (T.map τ)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N),
    T.map (R.map t) ≫ E.counitIso.hom.app N = E.counitIso.hom.app M ≫ t) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ),
    Nonempty ((R.obj M).obj.obj (op ((fieldFiniteEtaleToEtale k).obj A)) ≃+
      ((A.unop →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M))) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (A B : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ) (r : A ⟶ B)
    (h : (R.obj M).obj.obj (op ((fieldFiniteEtaleToEtale k).obj B)))
    (ξ : A.unop →ₐ[k] Ω),
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A
      ((R.obj M).obj.map ((fieldFiniteEtaleToEtale k).map r).op h) ξ =
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M B h (ξ.comp r.unop.hom.hom)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N)
    (A : (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ)
    (h : (R.obj M).obj.obj (op ((fieldFiniteEtaleToEtale k).obj A))) (ξ : A.unop →ₐ[k] Ω),
    fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω N A
      ((R.map t).hom.app (op ((fieldFiniteEtaleToEtale k).obj A)) h) ξ =
    DiscreteAbelianAction.homToAdd t
      (fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A h ξ)) ∧
  ∀ (F : Sheaf (Spec (.of k)).smallEtaleTopology AddCommGrpCat.{w})
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (c : F.obj.obj (op U)),
    (show FieldEquivariantFunctions.{u, w} k Ω U
      (T.obj ((liftCoefficients.{u, w} (Spec (.of k))).obj F)) from
      (E.unitIso.hom.app ((liftCoefficients.{u, w} (Spec (.of k))).obj F)).hom.app
        (op U) (ULift.up c)) z =
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      U (ULift.up z) ((liftCoefficients.{u, w} (Spec (.of k))).obj F).obj (ULift.up c)

/-- Let k and Ω be fields in universe u, with Ω a separable closure
of k, G = Gal(Ω/k), and c = max(u, w). Let E be the geometric-stalk
functor from AddCommGrpCat c-valued étale sheaves on Spec k to discrete
continuous G-modules.
Let Φ send a G-module M to the sheaf of G-equivariant functions
U(Ω) → M on étale k-schemes U. Write η and ε for the unit and counit
of E ⊣ Φ.
The stalk and equivariant-function inverse form an equivalence with
the stated unit, counit, both triangles and naturality. Its section
and germ formulas hold on all étale objects, on finite étale algebra
objects, and after coefficient lifting from w to c. -/
theorem original_field_sheaf_galois_equivalence :
    OriginalFieldSheafGaloisEquivalenceLaws.{u, w} k Ω := by
  refine ⟨rfl, rfl, rfl, rfl, (fun Q => inferInstance), (fun M => inferInstance),
    fieldSheafGaloisEquivalence_left_triangle.{u, w} k Ω,
    fieldSheafGaloisEquivalence_right_triangle.{u, w} k Ω,
    fieldSheafGaloisEquivalence_unit_germ.{u, w} k Ω,
    fieldSheafGaloisEquivalence_counit_germ.{u, w} k Ω,
    fieldSheafGaloisEquivalence_inverse_value.{u, w} k Ω, ?_, ?_, ?_, ?_,
    (fun M A => ⟨fieldSheafGaloisEquivalence_finite_value.{u, w} k Ω M A⟩),
    ?_, ?_, fieldSheafGaloisEquivalence_original_unit_germ.{u, w} k Ω⟩
  · intro M U V r h z
    exact fieldSheafGaloisEquivalence_inverse_restrict.{u, w} k Ω M r h z
  · intro M N t U h z
    exact fieldSheafGaloisEquivalence_inverse_map.{u, w} k Ω t U h z
  · intro Q Q' τ
    exact fieldEquivariantStalkUnit_naturality.{u, w} k Ω τ
  · intro M N t
    exact fieldEquivariantStalkCounit_naturality.{u, w} k Ω t
  · intro M A B r h ξ
    exact fieldSheafGaloisEquivalence_finite_restrict.{u, w} k Ω M r h ξ
  · intro M N t A h ξ
    exact fieldSheafGaloisEquivalence_finite_map.{u, w} k Ω t A h ξ

end AlgebraicGeometry.Scheme.DerivedSections
