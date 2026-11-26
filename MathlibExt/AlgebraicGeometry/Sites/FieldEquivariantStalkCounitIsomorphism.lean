/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.FieldEquivariantStalkAdjunction
public import Mathlib.FieldTheory.Normal.Basic

/-!
# Finite Galois evaluation and the field stalk counit

Fix a field `k` with separable closure `Ω` and a discrete Galois coefficient `M` in universe
`max u w`. For a finite Galois intermediate field `L`, evaluation at the inclusion `L → Ω`
identifies equivariant embedding functions with the subgroup fixed by automorphisms fixing
`L`. The inverse sends an embedding extended by `g` to `g • m`.

The same evaluation identifies inverse-sheaf sections on the finite Galois étale object with
these fixed coefficients. It is natural in coefficient maps and field refinement. Every
element of a discrete coefficient has some finite Galois fixing field; the coefficient itself
may be infinite.

The geometric stalk counit is therefore bijective and defines a natural coefficient
isomorphism. Its inverse is additive, Galois equivariant, continuous, and represented by the
corresponding finite-stage section germ. Evaluation and inverse-germ formulas hold on
arbitrary étale objects.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
open scoped Topology
universe u w
namespace AlgebraicGeometry.Scheme.DerivedSections
attribute [local instance] IsSepClosure.sep_closed
variable (k Ω : Type u) [Field k] [Field Ω] [Algebra k Ω] [IsSepClosure k Ω]

/-- Inclusion of a finite Galois field into the prescribed closure.

A finite Galois intermediate field has its given `k`-algebra inclusion into `Ω`. -/
def fieldFiniteGaloisEmbedding (L : FiniteGaloisIntermediateField k Ω) : L →ₐ[k] Ω :=
  IsScalarTower.toAlgHom k L Ω

/-- Finite Galois embedding extends to a closure automorphism.

Every `k`-embedding of a finite Galois intermediate field into the separable closure extends
to an element of `Gal(Ω/k)`. -/
def fieldGaloisEmbeddingExtension (L : FiniteGaloisIntermediateField k Ω)
    (ξ : L →ₐ[k] Ω) : Gal(Ω/k) := by
  letI : Normal k Ω := (IsSepClosure.isGalois (k := k) (K := Ω)).to_normal
  exact AlgEquiv.ofBijective (ξ.liftNormal Ω) (AlgHom.normal_bijective k Ω Ω _)

/-- Automorphism extension agrees on the finite field.

On elements of the finite intermediate field, the chosen closure automorphism extension equals
the given embedding. -/
theorem fieldGaloisEmbeddingExtension_apply (L : FiniteGaloisIntermediateField k Ω)
    (ξ : L →ₐ[k] Ω) (x : L) :
    fieldGaloisEmbeddingExtension k Ω L ξ (algebraMap L Ω x) = ξ x := by
  let : Normal k Ω := (IsSepClosure.isGalois (k := k) (K := Ω)).to_normal
  simpa only [fieldGaloisEmbeddingExtension, AlgEquiv.coe_ofBijective,
    Algebra.algebraMap_self, RingHom.id_apply] using ξ.liftNormal_commutes Ω x

/-- Automorphism extension sends the fixed inclusion to the embedding.

The extension automorphism acting on the canonical inclusion gives the prescribed finite-field
embedding. -/
theorem fieldGaloisEmbeddingExtension_embedding (L : FiniteGaloisIntermediateField k Ω)
    (ξ : L →ₐ[k] Ω) :
    fieldGaloisEmbeddingExtension k Ω L ξ • fieldFiniteGaloisEmbedding k Ω L = ξ := by
  ext x
  exact fieldGaloisEmbeddingExtension_apply k Ω L ξ x

omit [IsSepClosure k Ω] in
/-- Fixing subgroup stabilizes the finite field inclusion.

A Galois automorphism belongs to the finite field's fixing subgroup exactly when it fixes the
canonical inclusion into `Ω`. -/
theorem fieldFiniteGalois_mem_fixingSubgroup_iff
    (L : FiniteGaloisIntermediateField k Ω) (g : Gal(Ω/k)) :
    g ∈ L.fixingSubgroup ↔
      g • fieldFiniteGaloisEmbedding k Ω L = fieldFiniteGaloisEmbedding k Ω L := by
  rw [IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro hg
    ext x
    exact hg x x.property
  · intro hg x hx
    exact congrArg (fun ξ : L →ₐ[k] Ω => ξ ⟨x, hx⟩) hg

/-- Coefficient invariants of a finite Galois fixing subgroup.

Take the additive subgroup of a discrete coefficient fixed by every automorphism fixing the
finite Galois field. -/
def fieldFiniteGaloisModuleInvariants
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    AddSubgroup (DiscreteAbelianAction.underlying M) where
  carrier := {m | ∀ g : Gal(Ω/k), g ∈ L.fixingSubgroup → g • m = m}
  zero_mem' := fun g _ => smul_zero g
  add_mem' := fun hx hy g hg => by rw [smul_add, hx g hg, hy g hg]
  neg_mem' := fun hx g hg => by rw [smul_neg, hx g hg]

omit [IsSepClosure k Ω] in
/-- Equal embedding restrictions act equally on fixed coefficients.

If two automorphisms induce the same embedding of the finite field, their actions agree on a
coefficient element fixed by its fixing subgroup. -/
theorem fieldFiniteGalois_extensions_smul_eq
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (g h : Gal(Ω/k))
    (he : g • fieldFiniteGaloisEmbedding k Ω L =
      h • fieldFiniteGaloisEmbedding k Ω L) :
    g • (m : DiscreteAbelianAction.underlying M) =
      h • (m : DiscreteAbelianAction.underlying M) := by
  have hfix : (h⁻¹ * g) • fieldFiniteGaloisEmbedding k Ω L =
      fieldFiniteGaloisEmbedding k Ω L := by
    rw [mul_smul, he, inv_smul_smul]
  have hm := m.property (h⁻¹ * g)
    ((fieldFiniteGalois_mem_fixingSubgroup_iff k Ω L _).mpr hfix)
  have hs := congrArg (fun x : DiscreteAbelianAction.underlying M => h • x) hm
  simpa only [smul_smul, mul_inv_cancel_left] using hs

/-- Fixed coefficient as an equivariant embedding function.

For a fixed coefficient `m`, send an embedding `ξ` to `g • m`, where `g` extends `ξ`. The
fixing condition makes the value independent of the extension. -/
def fieldFiniteGaloisInvariantFunction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) :
    (L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M where
  toFun ξ := fieldGaloisEmbeddingExtension k Ω L ξ •
    (m : DiscreteAbelianAction.underlying M)
  map_smul' g ξ := by
    change fieldGaloisEmbeddingExtension k Ω L (g • ξ) •
        (m : DiscreteAbelianAction.underlying M) =
      g • (fieldGaloisEmbeddingExtension k Ω L ξ •
        (m : DiscreteAbelianAction.underlying M))
    rw [← mul_smul]
    apply fieldFiniteGalois_extensions_smul_eq.{u, w} k Ω M L m
    rw [fieldGaloisEmbeddingExtension_embedding, mul_smul,
      fieldGaloisEmbeddingExtension_embedding]

/-- Equivariant embedding function evaluates by any extension.

At an embedding induced by any automorphism `g`, the equivariant function associated to `m`
has value `g • m`. -/
theorem fieldFiniteGaloisInvariantFunction_apply_of_extension
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (ξ : L →ₐ[k] Ω) (g : Gal(Ω/k))
    (hg : g • fieldFiniteGaloisEmbedding k Ω L = ξ) :
    fieldFiniteGaloisInvariantFunction.{u, w} k Ω M L m ξ =
      g • (m : DiscreteAbelianAction.underlying M) := by
  apply fieldFiniteGalois_extensions_smul_eq.{u, w} k Ω M L m
  exact (fieldGaloisEmbeddingExtension_embedding k Ω L ξ).trans hg.symm

/-- Additive map from fixed coefficients to embedding functions.

The assignment from a fixing-subgroup invariant coefficient to its equivariant embedding
function is additive. -/
def fieldFiniteGaloisInvariantFunctionHom
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L →+
      ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) where
  toFun := fieldFiniteGaloisInvariantFunction.{u, w} k Ω M L
  map_zero' := by ext ξ; exact smul_zero _
  map_add' m m' := by ext ξ; exact smul_add _ _ _

/-- Evaluation at the finite field inclusion.

Evaluate an equivariant embedding function at the canonical inclusion to obtain an element
fixed by the finite field's fixing subgroup. -/
def fieldFiniteGaloisEvaluation
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) →+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L where
  toFun h := ⟨h (fieldFiniteGaloisEmbedding k Ω L), by
    intro g hg
    rw [← h.map_smul]
    exact congrArg h ((fieldFiniteGalois_mem_fixingSubgroup_iff k Ω L g).mp hg)⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' h h' := by apply Subtype.ext; rfl

/-- Equivariant embedding functions are the fixing subgroup invariants.

Evaluation at the inclusion and the extension-action construction are mutually inverse
additive maps. -/
def fieldFiniteGaloisEvaluationAddEquiv
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) ≃+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L where
  toFun := fieldFiniteGaloisEvaluation.{u, w} k Ω M L
  invFun := fieldFiniteGaloisInvariantFunctionHom.{u, w} k Ω M L
  left_inv h := by
    apply MulActionHom.ext
    intro ξ
    change fieldGaloisEmbeddingExtension k Ω L ξ •
      h (fieldFiniteGaloisEmbedding k Ω L) = h ξ
    rw [← h.map_smul, fieldGaloisEmbeddingExtension_embedding]
  right_inv m := by
    apply Subtype.ext
    change fieldFiniteGaloisInvariantFunction.{u, w} k Ω M L m
      (fieldFiniteGaloisEmbedding k Ω L) = (m : DiscreteAbelianAction.underlying M)
    simpa only [one_smul] using
      fieldFiniteGaloisInvariantFunction_apply_of_extension.{u, w} k Ω M L m
        (fieldFiniteGaloisEmbedding k Ω L) 1 (one_smul _ _)
  map_add' := (fieldFiniteGaloisEvaluation.{u, w} k Ω M L).map_add

/-- Each discrete coefficient element has a finite Galois fixing field.

For every element of any discrete Galois coefficient, some finite Galois intermediate field
has a fixing subgroup that fixes that element. -/
theorem fieldModule_element_finiteGalois
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (m : DiscreteAbelianAction.underlying M) :
    ∃ L : FiniteGaloisIntermediateField k Ω,
      m ∈ fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L := by
  let : Normal k Ω := (IsSepClosure.isGalois (k := k) (K := Ω)).to_normal
  have hopen := stabilizer_isOpen Gal(Ω/k) m
  have hmem : (MulAction.stabilizer Gal(Ω/k) m : Set Gal(Ω/k)) ∈ 𝓝 1 :=
    hopen.mem_nhds (by change (1 : Gal(Ω/k)) • m = m; exact one_smul _ _)
  obtain ⟨E, hfinite, hnormal, hE⟩ :=
    (krullTopology_mem_nhds_one_iff_of_normal k Ω
      (MulAction.stabilizer Gal(Ω/k) m)).mp hmem
  let : FiniteDimensional k E := hfinite
  let : Normal k E := hnormal
  let : Algebra.IsSeparable k E := Algebra.IsSeparable.of_algHom k Ω E.val
  let : IsGalois k E := { }
  let L : FiniteGaloisIntermediateField k Ω :=
    { toIntermediateField := E, finiteDimensional := hfinite, isGalois := inferInstance }
  exact ⟨L, fun g hg => hE hg⟩


/-- Coefficient maps preserve finite field invariants.

An equivariant coefficient morphism restricts to an additive map of the fixing-subgroup
invariant subgroups. -/
def fieldFiniteGaloisInvariantsMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L →+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω N L where
  toFun m := ⟨DiscreteAbelianAction.homToAdd t m, by
    intro g hg
    rw [← DiscreteAbelianAction.homToAdd_equivariant, m.property g hg]⟩
  map_zero' := by apply Subtype.ext; exact (DiscreteAbelianAction.homToAdd t).map_zero
  map_add' m m' := by apply Subtype.ext; exact (DiscreteAbelianAction.homToAdd t).map_add _ _

/-- Coefficient maps act on equivariant embedding functions.

Postcompose an equivariant embedding function with an equivariant coefficient map. -/
def fieldFiniteGaloisFunctionsMap
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω) :
    ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) →+
      ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying N) where
  toFun h := {
    toFun := fun ξ => DiscreteAbelianAction.homToAdd t (h ξ)
    map_smul' := fun g ξ => by
      rw [h.map_smul]
      exact DiscreteAbelianAction.homToAdd_equivariant t g (h ξ) }
  map_zero' := by ext ξ; exact (DiscreteAbelianAction.homToAdd t).map_zero
  map_add' h h' := by ext ξ; exact (DiscreteAbelianAction.homToAdd t).map_add _ _

/-- Embedding evaluation is coefficient natural.

Evaluation commutes with postcomposition on embedding functions and the induced map on fixed
coefficients. -/
theorem fieldFiniteGaloisEvaluation_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω)
    (h : (L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) :
    fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω N L
        (fieldFiniteGaloisFunctionsMap.{u, w} k Ω t L h) =
      fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L
        (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L h) := by
  apply Subtype.ext
  rfl

/-- Inverse embedding evaluation is coefficient natural.

The inverse evaluation commutes with coefficient maps and the corresponding postcomposition of
equivariant functions. -/
theorem fieldFiniteGaloisEvaluation_inverse_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) :
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω N L).symm
        (fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L m) =
      fieldFiniteGaloisFunctionsMap.{u, w} k Ω t L
        ((fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m) := by
  apply MulActionHom.ext
  intro ξ
  change fieldGaloisEmbeddingExtension k Ω L ξ • DiscreteAbelianAction.homToAdd t m =
    DiscreteAbelianAction.homToAdd t
      (fieldGaloisEmbeddingExtension k Ω L ξ • (m : DiscreteAbelianAction.underlying M))
  exact (DiscreteAbelianAction.homToAdd_equivariant t _ _).symm

/-- Restriction of embeddings along a finite field inclusion.

For `L ≤ L'`, restrict an embedding of `L'` by precomposition with the inclusion of `L`,
equivariantly for the Galois action. -/
def fieldFiniteGaloisEmbeddingRestriction
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L') :
    (L' →ₐ[k] Ω) →[Gal(Ω/k)] (L →ₐ[k] Ω) where
  toFun ξ := ξ.comp (IntermediateField.inclusion h)
  map_smul' g ξ := by ext x; rfl

/-- Pullback of embedding functions along field refinement.

Precompose a function on embeddings of `L` with restriction from embeddings of `L'` to obtain
the refined equivariant function. -/
def fieldFiniteGaloisFunctionsRestriction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L') :
    ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) →+
      ((L' →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) where
  toFun f := f.comp (fieldFiniteGaloisEmbeddingRestriction k Ω h)
  map_zero' := by ext ξ; rfl
  map_add' f f' := by ext ξ; rfl

/-- Invariants enlarge along finite Galois field refinement.

For `L ≤ L'`, inclusion sends coefficients fixed by the fixing subgroup of `L` to those fixed
by the smaller fixing subgroup of `L'`. -/
def fieldFiniteGaloisInvariantsInclusion
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L') :
    fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L →+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L' where
  toFun m := ⟨m, fun g hg => m.property g (IntermediateField.fixingSubgroup_le h hg)⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' m m' := by apply Subtype.ext; rfl

/-- Embedding evaluation respects field refinement.

Evaluation of a refined equivariant function equals inclusion of its evaluation into the
larger invariant subgroup. -/
theorem fieldFiniteGaloisEvaluation_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L')
    (f : (L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) :
    fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L'
        (fieldFiniteGaloisFunctionsRestriction.{u, w} k Ω M h f) =
      fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h
        (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L f) := by
  apply Subtype.ext
  rfl

/-- Inverse embedding evaluation respects field refinement.

Inverse evaluation after invariant inclusion equals pullback of the equivariant embedding
function along restriction. -/
theorem fieldFiniteGaloisEvaluation_inverse_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L')
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) :
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L').symm
        (fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h m) =
      fieldFiniteGaloisFunctionsRestriction.{u, w} k Ω M h
        ((fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m) := by
  apply MulActionHom.ext
  intro ξ
  let g := fieldGaloisEmbeddingExtension k Ω L' ξ
  have hg : g • fieldFiniteGaloisEmbedding k Ω L =
      ξ.comp (IntermediateField.inclusion h) := by
    ext x
    exact fieldGaloisEmbeddingExtension_apply k Ω L' ξ (IntermediateField.inclusion h x)
  change g • (m : DiscreteAbelianAction.underlying M) =
    fieldFiniteGaloisInvariantFunction.{u, w} k Ω M L m
      (ξ.comp (IntermediateField.inclusion h))
  exact (fieldFiniteGaloisInvariantFunction_apply_of_extension.{u, w} k Ω M L m _ g hg).symm

/-- Finite Galois field in the opposite finite étale category.

Regard the finite Galois intermediate field as an object of the opposite finite étale algebra
category for the spectrum functor. -/
def fieldFiniteGaloisAlgebra (L : FiniteGaloisIntermediateField k Ω) :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ := by
  let : Module.Finite k L := L.finiteDimensional
  have h : Etale (Spec.algebraMap k L) := (fieldFiniteGaloisEtale k Ω L).prop
  let : Algebra.Etale k L := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h)
  exact op (CommAlgCat.FiniteEtale.of k L)

/-- Finite Galois algebra gives its étale scheme object.

The finite étale-to-scheme functor sends the opposite algebra object to the specified finite
Galois étale object. -/
theorem fieldFiniteGaloisAlgebra_etale (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteEtaleToEtale k).obj (fieldFiniteGaloisAlgebra k Ω L) =
      fieldFiniteGaloisEtale k Ω L := rfl

/-- Finite Galois point corresponds to the fixed embedding.

The finite étale geometric-fiber equivalence sends the specified finite Galois point to the
canonical field inclusion. -/
theorem fieldFiniteGaloisAlgebra_point (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteEtaleFiberEquiv k Ω (fieldFiniteGaloisAlgebra k Ω L)
        (fieldFiniteGaloisPoint k Ω L) = fieldFiniteGaloisEmbedding k Ω L := by
  change Spec.homEquivAlgHom (Spec.homEquivAlgHom.symm
    (IsScalarTower.toAlgHom k L Ω)) = IsScalarTower.toAlgHom k L Ω
  exact Spec.homEquivAlgHom.apply_symm_apply _


/-- Inverse geometric fiber coordinate gives the finite Galois point.

The inverse fiber isomorphism sends the canonical finite-field embedding to the specified
geometric point. -/
theorem fieldFiniteGaloisAlgebra_point_inverse (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteEtaleGeometricFiberIso k Ω).inv.app (fieldFiniteGaloisAlgebra k Ω L)
        (fieldFiniteGaloisEmbedding k Ω L) = fieldFiniteGaloisPoint k Ω L := by
  change (fieldFiniteEtaleFiberEquiv k Ω (fieldFiniteGaloisAlgebra k Ω L)).symm
    (fieldFiniteGaloisEmbedding k Ω L) = fieldFiniteGaloisPoint k Ω L
  simpa only [fieldFiniteGaloisAlgebra_point] using
    (fieldFiniteEtaleFiberEquiv k Ω (fieldFiniteGaloisAlgebra k Ω L)).symm_apply_apply
      (fieldFiniteGaloisPoint k Ω L)

/-- Embedding evaluation has the inclusion value.

The underlying value of the evaluation equivalence is the equivariant function evaluated at
the canonical inclusion. -/
theorem fieldFiniteGaloisEvaluation_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (h : (L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) :
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L h :
      DiscreteAbelianAction.underlying M) = h (fieldFiniteGaloisEmbedding k Ω L) := rfl

/-- Inverse embedding evaluation has the extension action value.

For any automorphism `g` inducing an embedding `ξ`, inverse evaluation of a fixed coefficient
at `ξ` is `g • m`. -/
theorem fieldFiniteGaloisEvaluation_symm_extension
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (ξ : L →ₐ[k] Ω) (g : Gal(Ω/k))
    (hg : g • fieldFiniteGaloisEmbedding k Ω L = ξ) :
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m ξ =
      g • (m : DiscreteAbelianAction.underlying M) :=
  fieldFiniteGaloisInvariantFunction_apply_of_extension.{u, w} k Ω M L m ξ g hg

/-- Finite Galois inverse sheaf sections are fixing subgroup invariants.

Sections of the invariant inverse sheaf on the finite Galois étale object are additively
equivalent to coefficients fixed by the associated fixing subgroup. -/
def fieldFiniteGaloisSectionEvaluationAddEquiv
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op (fieldFiniteGaloisEtale k Ω L)) ≃+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L :=
  (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M
    (fieldFiniteGaloisAlgebra k Ω L)).trans
      (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L)

/-- Finite Galois section evaluation uses its geometric point.

The section evaluation equivalence takes an equivariant section to its value at the canonical
finite Galois point. -/
theorem fieldFiniteGaloisSectionEvaluation_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M) :
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L h :
      DiscreteAbelianAction.underlying M) = h (fieldFiniteGaloisPoint k Ω L) := by
  change h ((fieldFiniteEtaleGeometricFiberIso k Ω).inv.app
    (fieldFiniteGaloisAlgebra k Ω L) (fieldFiniteGaloisEmbedding k Ω L)) =
      h (fieldFiniteGaloisPoint k Ω L)
  exact congrArg h (fieldFiniteGaloisAlgebra_point_inverse k Ω L)

/-- Inverse finite Galois section at an embedding point.

At a geometric point corresponding to an embedding extended by `g`, the inverse section of a
fixed coefficient has value `g • m`. -/
theorem fieldFiniteGaloisSectionEvaluation_symm_point
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (z : (fieldGeometricPoint k Ω).fiber.obj (fieldFiniteGaloisEtale k Ω L))
    (g : Gal(Ω/k))
    (hg : g • fieldFiniteGaloisEmbedding k Ω L =
      (fieldFiniteEtaleGeometricFiberIso k Ω).hom.app (fieldFiniteGaloisAlgebra k Ω L) z) :
    (show FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M from
      (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m) z =
        g • (m : DiscreteAbelianAction.underlying M) := by
  change (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m
    ((fieldFiniteEtaleGeometricFiberIso k Ω).hom.app
      (fieldFiniteGaloisAlgebra k Ω L) z) = _
  exact fieldFiniteGaloisEvaluation_symm_extension.{u, w} k Ω M L m _ g hg

/-- Finite Galois section evaluation is coefficient natural.

The inverse-sheaf coefficient map commutes with finite-stage evaluation and the map on fixing-
subgroup invariants. -/
theorem fieldFiniteGaloisSectionEvaluation_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M) :
    fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω N L
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
          (op (fieldFiniteGaloisEtale k Ω L)) h) =
      fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L
        (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L h) := by
  apply Subtype.ext
  rfl

/-- Inverse finite Galois section evaluation is coefficient natural.

The inverse evaluation commutes with coefficient maps and their inverse-sheaf section maps. -/
theorem fieldFiniteGaloisSectionEvaluation_inverse_map
    {M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)} (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) :
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω N L).symm
        (fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L m) =
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
        (op (fieldFiniteGaloisEtale k Ω L))
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m) := by
  apply (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω N L).injective
  calc
    _ = fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L m :=
      (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω N L).apply_symm_apply _
    _ = fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L
        (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L
          ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m)) :=
      congrArg (fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L)
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).apply_symm_apply m).symm
    _ = _ := (fieldFiniteGaloisSectionEvaluation_map.{u, w} k Ω t L _).symm

/-- Finite Galois section evaluation respects restriction.

Restriction to a larger finite Galois étale field corresponds under evaluation to inclusion of
invariant coefficients. -/
theorem fieldFiniteGaloisSectionEvaluation_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L')
    (c : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M) :
    fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L'
        (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
          (fieldFiniteGaloisInclusion k Ω h).op c) =
      fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h
        (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L c) := by
  let c' : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L') M :=
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
      (fieldFiniteGaloisInclusion k Ω h).op c
  have hr : c' (fieldFiniteGaloisPoint k Ω L') = c (fieldFiniteGaloisPoint k Ω L) := by
    change c ((fieldGeometricPoint k Ω).fiber.map (fieldFiniteGaloisInclusion k Ω h)
      (fieldFiniteGaloisPoint k Ω L')) = c (fieldFiniteGaloisPoint k Ω L)
    exact congrArg c (fieldFiniteGaloisInclusion_point k Ω h)
  apply Subtype.ext
  exact (fieldFiniteGaloisSectionEvaluation_apply.{u, w} k Ω M L' c').trans
    (hr.trans (fieldFiniteGaloisSectionEvaluation_apply.{u, w} k Ω M L c).symm)

/-- Inverse finite Galois section evaluation respects restriction.

The inverse section for an included invariant coefficient is the restriction of its earlier
finite-stage inverse section. -/
theorem fieldFiniteGaloisSectionEvaluation_inverse_restrict
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L')
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) :
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L').symm
        (fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h m) =
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
        (fieldFiniteGaloisInclusion k Ω h).op
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m) := by
  apply (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L').injective
  calc
    _ = fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h m :=
      (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L').apply_symm_apply _
    _ = fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h
        (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L
          ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m)) :=
      congrArg (fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h)
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).apply_symm_apply m).symm
    _ = _ := (fieldFiniteGaloisSectionEvaluation_restrict.{u, w} k Ω M h _).symm

/-- Field stalk counit has zero kernel.

An inverse-sheaf stalk element whose counit value is zero is itself zero. -/
theorem fieldEquivariantStalkCounit_eq_zero
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (x : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)))
    (hx : DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) x = 0) : x = 0 := by
  let Q := (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M
  let Φ := smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)
  obtain ⟨L, c, hc⟩ := fieldGeometricStalk_finite_rep.{u, w} k Ω Q x
  let c0 : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M := c
  let p : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M →+
      DiscreteAbelianAction.underlying ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
    (Φ.toPresheafFiber (fieldFiniteGaloisEtale k Ω L)
      (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj).hom
  have hp : p c0 = x := hc
  have hval : c0 (fieldFiniteGaloisPoint k Ω L) = 0 :=
    (fieldEquivariantStalkCounit_germ.{u, w} k Ω M (fieldFiniteGaloisEtale k Ω L)
      (fieldFiniteGaloisPoint k Ω L) c0).symm.trans
        ((congrArg (DiscreteAbelianAction.homToAdd
          ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) hp).trans hx)
  have he : fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L c0 = 0 := by
    apply Subtype.ext
    exact (fieldFiniteGaloisSectionEvaluation_apply.{u, w} k Ω M L c0).trans hval
  have hc0 : c0 = 0 :=
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).injective
      (he.trans (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).map_zero.symm)
  exact hp.symm.trans ((congrArg p hc0).trans p.map_zero)

/-- Field stalk counit is injective.

The underlying additive map of the equivariant stalk counit is injective. -/
theorem fieldEquivariantStalkCounit_injective
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Function.Injective (DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply fieldEquivariantStalkCounit_eq_zero.{u, w} k Ω M (x - y)
  rw [map_sub, hxy, sub_self]

/-- Field stalk counit is surjective.

Every discrete coefficient element is the counit value of a germ represented at a suitable
finite Galois field. -/
theorem fieldEquivariantStalkCounit_surjective
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Function.Surjective (DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) := by
  intro m
  obtain ⟨L, hm⟩ := fieldModule_element_finiteGalois.{u, w} k Ω M m
  let mL : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L := ⟨m, hm⟩
  let c : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M :=
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm mL
  let Q := (fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M
  let p : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M →+
      DiscreteAbelianAction.underlying ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj Q) :=
    ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
      (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L)) Q.obj).hom
  have hval : c (fieldFiniteGaloisPoint k Ω L) = m :=
    (fieldFiniteGaloisSectionEvaluation_apply.{u, w} k Ω M L c).symm.trans
      (congrArg Subtype.val
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).apply_symm_apply mL))
  exact ⟨p c, (fieldEquivariantStalkCounit_germ.{u, w} k Ω M
    (fieldFiniteGaloisEtale k Ω L) (fieldFiniteGaloisPoint k Ω L) c).trans hval⟩

/-- Field stalk counit is bijective.

The counit is bijective on underlying additive-group carriers. -/
theorem fieldEquivariantStalkCounit_bijective
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Function.Bijective (DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) :=
  ⟨fieldEquivariantStalkCounit_injective.{u, w} k Ω M,
    fieldEquivariantStalkCounit_surjective.{u, w} k Ω M⟩

/-- Field stalk counit is an isomorphism of coefficients.

The proved counit bijection defines an isomorphism from the geometric Galois stalk of the
inverse sheaf to its coefficient. -/
def fieldEquivariantStalkCounitIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)) ≅ M :=
  DiscreteAbelianAction.isoOfBijective ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
    (fieldEquivariantStalkCounit_bijective.{u, w} k Ω M)

/-- Field counit isomorphism retains the adjunction map.

The forward morphism of the counit isomorphism is the specified adjunction counit component. -/
@[simp] theorem fieldEquivariantStalkCounitIso_hom
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldEquivariantStalkCounitIso.{u, w} k Ω M).hom =
      (fieldEquivariantStalkCounit.{u, w} k Ω).app M := rfl

/-- Adjunction counit is invertible on every field coefficient.

Every component of the equivariant field stalk adjunction counit is an isomorphism. -/
instance fieldEquivariantStalkCounit_isIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    IsIso ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) :=
  (fieldEquivariantStalkCounitIso.{u, w} k Ω M).isIso_hom

/-- Field stalk counit forms a natural isomorphism.

The coefficient-natural counit isomorphisms give an isomorphism from inverse sheaf followed by
geometric stalk to the identity coefficient functor. -/
def fieldEquivariantStalkCounitNatIso :
    fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω ⋙
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
        𝟭 (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :=
  NatIso.ofComponents (fieldEquivariantStalkCounitIso.{u, w} k Ω)
    (by intro M N t; exact (fieldEquivariantStalkCounit.{u, w} k Ω).naturality t)

/-- Natural field counit isomorphism has the given counit.

Its forward natural transformation equals the adjunction counit. -/
theorem fieldEquivariantStalkCounitNatIso_hom :
    (fieldEquivariantStalkCounitNatIso.{u, w} k Ω).hom =
      fieldEquivariantStalkCounit.{u, w} k Ω := by
  apply NatTrans.ext
  rfl

/-- Counit inverse after counit is the identity.

Applying the counit to a stalk element and then its inverse recovers that element. -/
theorem fieldEquivariantStalkCounit_inverse_after
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (x : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M))) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv
      (DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) x) = x := by
  have h := congrArg (fun t => DiscreteAbelianAction.homToAdd t x)
    (fieldEquivariantStalkCounitIso.{u, w} k Ω M).hom_inv_id
  simpa only [DiscreteAbelianAction.homToAdd_comp, DiscreteAbelianAction.homToAdd_id,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, fieldEquivariantStalkCounitIso_hom] using h

/-- Counit after its inverse is the identity.

Applying the inverse counit to a coefficient element and then the counit recovers that
element. -/
theorem fieldEquivariantStalkCounit_after_inverse
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (m : DiscreteAbelianAction.underlying M) :
    DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
      (DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m) = m := by
  have h := congrArg (fun t => DiscreteAbelianAction.homToAdd t m)
    (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv_hom_id
  simpa only [DiscreteAbelianAction.homToAdd_comp, DiscreteAbelianAction.homToAdd_id,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, fieldEquivariantStalkCounitIso_hom] using h

/-- Inverse field counit is additive.

The inverse counit sends a sum of coefficient elements to the sum of their inverse images. -/
theorem fieldEquivariantStalkCounit_inverse_add
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (m m' : DiscreteAbelianAction.underlying M) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (m + m') =
      DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m +
        DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m' :=
  (DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv).map_add _ _

/-- Inverse field counit is Galois equivariant.

The inverse counit commutes with the Galois action on each coefficient element. -/
theorem fieldEquivariantStalkCounit_inverse_equivariant
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k))
    (m : DiscreteAbelianAction.underlying M) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (g • m) =
      g • DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m :=
  DiscreteAbelianAction.homToAdd_equivariant _ g m

/-- Inverse field counit is continuous.

The inverse counit is continuous from the discrete coefficient topology. -/
theorem fieldEquivariantStalkCounit_inverse_continuous
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Continuous (DiscreteAbelianAction.homToAdd
      (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv) := continuous_of_discreteTopology

/-- Inverse field counit recovers every evaluation germ.

The inverse of the value `h z` is the geometric germ of the equivariant inverse-sheaf section
`h` at `z`. -/
theorem fieldEquivariantStalkCounit_inverse_germ
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
    (h : FieldEquivariantFunctions.{u, w} k Ω U M) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (h z) =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
        (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj h := by
  let x : DiscreteAbelianAction.underlying
      ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)) :=
    (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
      (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj h
  let f := DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
  let j := DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv
  have he : f x = h z := fieldEquivariantStalkCounit_germ.{u, w} k Ω M U z h
  exact (congrArg j he.symm).trans
    (fieldEquivariantStalkCounit_inverse_after.{u, w} k Ω M x)

/-- Inverse field counit has its finite Galois stage representative.

For a coefficient fixed at finite field `L`, its inverse counit image is the germ at the
canonical `L`-point of the inverse finite-stage evaluation section. -/
theorem fieldEquivariantStalkCounit_inverse_stage
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m =
      (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
        (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))
        ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m) := by
  let c : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M :=
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m
  let j := DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv
  have hval : c (fieldFiniteGaloisPoint k Ω L) = (m : DiscreteAbelianAction.underlying M) :=
    (fieldFiniteGaloisSectionEvaluation_apply.{u, w} k Ω M L c).symm.trans
      (congrArg Subtype.val
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).apply_symm_apply m))
  exact (congrArg j hval.symm).trans
    (fieldEquivariantStalkCounit_inverse_germ.{u, w} k Ω M
      (fieldFiniteGaloisEtale k Ω L) (fieldFiniteGaloisPoint k Ω L) c)

/-- Full finite Galois evaluation and naturality laws.

These laws include embedding extension, fixing subgroups, evaluation and inverse values,
finite fixing fields for elements, and forward/inverse naturality under coefficient maps and
field refinement, both for functions and inverse-sheaf sections. -/
def FieldFiniteGaloisEvaluationLaws : Prop :=
  (∀ (L : FiniteGaloisIntermediateField k Ω) (ξ : L →ₐ[k] Ω),
    fieldGaloisEmbeddingExtension k Ω L ξ • fieldFiniteGaloisEmbedding k Ω L = ξ) ∧
  (∀ (L : FiniteGaloisIntermediateField k Ω) (g : Gal(Ω/k)), g ∈ L.fixingSubgroup ↔
    g • fieldFiniteGaloisEmbedding k Ω L = fieldFiniteGaloisEmbedding k Ω L) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (h : (L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M),
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L h :
      DiscreteAbelianAction.underlying M) = h (fieldFiniteGaloisEmbedding k Ω L)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (ξ : L →ₐ[k] Ω) (g : Gal(Ω/k)) (_hg : g • fieldFiniteGaloisEmbedding k Ω L = ξ),
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m ξ =
      g • (m : DiscreteAbelianAction.underlying M)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (m : DiscreteAbelianAction.underlying M), ∃ L : FiniteGaloisIntermediateField k Ω,
      m ∈ fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω),
    (∀ h, fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω N L
      (fieldFiniteGaloisFunctionsMap.{u, w} k Ω t L h) =
      fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L
        (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L h)) ∧
    (∀ m, (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω N L).symm
      (fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L m) =
      fieldFiniteGaloisFunctionsMap.{u, w} k Ω t L
        ((fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m))) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L L' : FiniteGaloisIntermediateField k Ω) (h : L ≤ L'),
    (∀ f, fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L'
      (fieldFiniteGaloisFunctionsRestriction.{u, w} k Ω M h f) =
      fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h
        (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L f)) ∧
    (∀ m, (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L').symm
      (fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h m) =
      fieldFiniteGaloisFunctionsRestriction.{u, w} k Ω M h
        ((fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m))) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (h : FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M),
    (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L h :
      DiscreteAbelianAction.underlying M) = h (fieldFiniteGaloisPoint k Ω L)) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (z : (fieldGeometricPoint k Ω).fiber.obj (fieldFiniteGaloisEtale k Ω L))
    (g : Gal(Ω/k)) (_hg : g • fieldFiniteGaloisEmbedding k Ω L =
      (fieldFiniteEtaleGeometricFiberIso k Ω).hom.app (fieldFiniteGaloisAlgebra k Ω L) z),
    (show FieldEquivariantFunctions.{u, w} k Ω (fieldFiniteGaloisEtale k Ω L) M from
      (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m) z =
        g • (m : DiscreteAbelianAction.underlying M)) ∧
  (∀ (M N : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (t : M ⟶ N)
    (L : FiniteGaloisIntermediateField k Ω),
    (∀ h, fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω N L
      (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
        (op (fieldFiniteGaloisEtale k Ω L)) h) =
      fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L
        (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L h)) ∧
    (∀ m, (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω N L).symm
      (fieldFiniteGaloisInvariantsMap.{u, w} k Ω t L m) =
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).map t).hom.app
        (op (fieldFiniteGaloisEtale k Ω L))
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m))) ∧
  (∀ (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L L' : FiniteGaloisIntermediateField k Ω) (h : L ≤ L'),
    (∀ c, fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L'
      (((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
        (fieldFiniteGaloisInclusion k Ω h).op c) =
      fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h
        (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L c)) ∧
    (∀ m, (fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L').symm
      (fieldFiniteGaloisInvariantsInclusion.{u, w} k Ω M h m) =
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.map
        (fieldFiniteGaloisInclusion k Ω h).op
        ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m)))

/-- Finite Galois evaluation satisfies its full laws.

The finite-field evaluation constructions satisfy all extension, fixed-element, value,
coefficient-map, and refinement identities. -/
theorem fieldFiniteGaloisEvaluation_laws : FieldFiniteGaloisEvaluationLaws.{u, w} k Ω := by
  refine ⟨fieldGaloisEmbeddingExtension_embedding k Ω,
    fieldFiniteGalois_mem_fixingSubgroup_iff k Ω,
    fieldFiniteGaloisEvaluation_apply.{u, w} k Ω,
    fieldFiniteGaloisEvaluation_symm_extension.{u, w} k Ω,
    fieldModule_element_finiteGalois.{u, w} k Ω, ?_, ?_,
    fieldFiniteGaloisSectionEvaluation_apply.{u, w} k Ω,
    fieldFiniteGaloisSectionEvaluation_symm_point.{u, w} k Ω, ?_, ?_⟩
  · exact fun _ _ t L => ⟨fieldFiniteGaloisEvaluation_map.{u, w} k Ω t L,
      fieldFiniteGaloisEvaluation_inverse_map.{u, w} k Ω t L⟩
  · exact fun M _ _ h => ⟨fieldFiniteGaloisEvaluation_restrict.{u, w} k Ω M h,
      fieldFiniteGaloisEvaluation_inverse_restrict.{u, w} k Ω M h⟩
  · exact fun _ _ t L => ⟨fieldFiniteGaloisSectionEvaluation_map.{u, w} k Ω t L,
      fieldFiniteGaloisSectionEvaluation_inverse_map.{u, w} k Ω t L⟩
  · exact fun M _ _ h => ⟨fieldFiniteGaloisSectionEvaluation_restrict.{u, w} k Ω M h,
      fieldFiniteGaloisSectionEvaluation_inverse_restrict.{u, w} k Ω M h⟩

/-- Full finite Galois and field counit isomorphism laws.

The counit is bijective and invertible with its given forward map, an additive equivariant
continuous inverse, both inverse identities, and the evaluation-germ and finite-stage
formulas. Its natural isomorphism has the given counit transformation. -/
def FieldEquivariantStalkCounitIsomorphismLaws : Prop :=
  FieldFiniteGaloisEvaluationLaws.{u, w} k Ω ∧
  (∀ M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k),
    Function.Bijective (DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) ∧
    IsIso ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) ∧
    (fieldEquivariantStalkCounitIso.{u, w} k Ω M).hom =
      (fieldEquivariantStalkCounit.{u, w} k Ω).app M ∧
    Continuous (DiscreteAbelianAction.homToAdd
      (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv) ∧
    (∀ m m', DiscreteAbelianAction.homToAdd
      (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (m + m') =
      DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m +
        DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m') ∧
    (∀ (g : Gal(Ω/k)) (m : DiscreteAbelianAction.underlying M),
      DiscreteAbelianAction.homToAdd
      (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (g • m) =
      g • DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m) ∧
    (∀ x, DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv
      (DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) x) = x) ∧
    (∀ m, DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
      (DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m) = m) ∧
    (∀ (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (h : FieldEquivariantFunctions.{u, w} k Ω U M),
      DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
        ((smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
          (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj h) = h z) ∧
    (∀ (U : (Spec (.of k)).Etale) (z : (fieldGeometricPoint k Ω).fiber.obj U)
      (h : FieldEquivariantFunctions.{u, w} k Ω U M),
      DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (h z) =
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber U
          (ULift.up z) ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj h) ∧
    (∀ (L : FiniteGaloisIntermediateField k Ω)
      (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L),
      DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m =
        (smallEtaleGeometricPointCommon.{u, w} (Spec.algebraMap k Ω)).toPresheafFiber
          (fieldFiniteGaloisEtale k Ω L) (ULift.up (fieldFiniteGaloisPoint k Ω L))
          ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj
          ((fieldFiniteGaloisSectionEvaluationAddEquiv.{u, w} k Ω M L).symm m))) ∧
  (fieldEquivariantStalkCounitNatIso.{u, w} k Ω).hom = fieldEquivariantStalkCounit.{u, w} k Ω

/-- Field stalk counit satisfies all isomorphism laws.

The finite Galois evaluation and equivariant field counit constructions satisfy their complete
value, naturality, inverse, and finite-stage normalization laws. -/
theorem original_field_equivariant_stalk_counit_isomorphism :
    FieldEquivariantStalkCounitIsomorphismLaws.{u, w} k Ω := by
  refine ⟨fieldFiniteGaloisEvaluation_laws.{u, w} k Ω, ?_,
    fieldEquivariantStalkCounitNatIso_hom.{u, w} k Ω⟩
  intro M
  exact ⟨fieldEquivariantStalkCounit_bijective.{u, w} k Ω M, inferInstance,
    fieldEquivariantStalkCounitIso_hom.{u, w} k Ω M,
    fieldEquivariantStalkCounit_inverse_continuous.{u, w} k Ω M,
    fieldEquivariantStalkCounit_inverse_add.{u, w} k Ω M,
    fieldEquivariantStalkCounit_inverse_equivariant.{u, w} k Ω M,
    fieldEquivariantStalkCounit_inverse_after.{u, w} k Ω M,
    fieldEquivariantStalkCounit_after_inverse.{u, w} k Ω M,
    fieldEquivariantStalkCounit_germ.{u, w} k Ω M,
    fieldEquivariantStalkCounit_inverse_germ.{u, w} k Ω M,
    fieldEquivariantStalkCounit_inverse_stage.{u, w} k Ω M⟩

end AlgebraicGeometry.Scheme.DerivedSections
