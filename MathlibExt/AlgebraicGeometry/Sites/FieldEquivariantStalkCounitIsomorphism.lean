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

/-! # Finite Galois evaluation and the actual field counit

All intermediate fields are in the prescribed separable closure. Module objects
and their original actions may be infinite; each element has its own fixing field.
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

/-- The original inclusion of a finite Galois field into the chosen closure. -/
def fieldFiniteGaloisEmbedding (L : FiniteGaloisIntermediateField k Ω) : L →ₐ[k] Ω :=
  IsScalarTower.toAlgHom k L Ω

/-- Every original embedding extends to an actual automorphism of the SAME closure. -/
def fieldGaloisEmbeddingExtension (L : FiniteGaloisIntermediateField k Ω)
    (ξ : L →ₐ[k] Ω) : Gal(Ω/k) := by
  letI : Normal k Ω := (IsSepClosure.isGalois (k := k) (K := Ω)).to_normal
  exact AlgEquiv.ofBijective (ξ.liftNormal Ω) (AlgHom.normal_bijective k Ω Ω _)

theorem fieldGaloisEmbeddingExtension_apply (L : FiniteGaloisIntermediateField k Ω)
    (ξ : L →ₐ[k] Ω) (x : L) :
    fieldGaloisEmbeddingExtension k Ω L ξ (algebraMap L Ω x) = ξ x := by
  let : Normal k Ω := (IsSepClosure.isGalois (k := k) (K := Ω)).to_normal
  simpa only [fieldGaloisEmbeddingExtension, AlgEquiv.coe_ofBijective,
    Algebra.algebraMap_self, RingHom.id_apply] using ξ.liftNormal_commutes Ω x

theorem fieldGaloisEmbeddingExtension_embedding (L : FiniteGaloisIntermediateField k Ω)
    (ξ : L →ₐ[k] Ω) :
    fieldGaloisEmbeddingExtension k Ω L ξ • fieldFiniteGaloisEmbedding k Ω L = ξ := by
  ext x
  exact fieldGaloisEmbeddingExtension_apply k Ω L ξ x

omit [IsSepClosure k Ω] in
/-- The actual fixing subgroup is the stabilizer of the original inclusion. -/
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

/-- The possibly infinite additive group fixed by the actual finite-field subgroup. -/
def fieldFiniteGaloisModuleInvariants
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    AddSubgroup (DiscreteAbelianAction.underlying M) where
  carrier := {m | ∀ g : Gal(Ω/k), g ∈ L.fixingSubgroup → g • m = m}
  zero_mem' := fun g _ => smul_zero g
  add_mem' := fun hx hy g hg => by rw [smul_add, hx g hg, hy g hg]
  neg_mem' := fun hx g hg => by rw [smul_neg, hx g hg]

omit [IsSepClosure k Ω] in
/-- Extensions with the SAME original restriction give the SAME value on invariants. -/
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

/-- An invariant element gives its literal equivariant function on original embeddings. -/
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

/-- The inverse formula is valid for EVERY actual automorphism extending the embedding. -/
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

/-- `fieldFiniteGaloisInvariantFunction` as an additive map: an element of `M` fixed by the
subgroup fixing `L` gives a `Gal(Ω/k)`-equivariant function on the embeddings `L →ₐ[k] Ω`. -/
def fieldFiniteGaloisInvariantFunctionHom
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L →+
      ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) where
  toFun := fieldFiniteGaloisInvariantFunction.{u, w} k Ω M L
  map_zero' := by ext ξ; exact smul_zero _
  map_add' m m' := by ext ξ; exact smul_add _ _ _

/-- Evaluation at the original inclusion lands in its actual fixed additive group. -/
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

/-- EVERY finite Galois stage has its actual original-embedding evaluation equivalence. -/
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

/-- Each actual module element has its own finite Galois fixing field in the SAME closure. -/
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


/-- Every actual module arrow maps the SAME finite-field invariant groups. -/
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

/-- The original additive module map postcomposes literal equivariant embedding functions. -/
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

/-- All module morphisms commute with the SAME original-stage evaluation. -/
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

/-- The actual inverse-stage functions are natural in EVERY module arrow. -/
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

/-- Every actual field inclusion restricts original embeddings by that SAME algebra map. -/
def fieldFiniteGaloisEmbeddingRestriction
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L') :
    (L' →ₐ[k] Ω) →[Gal(Ω/k)] (L →ₐ[k] Ω) where
  toFun ξ := ξ.comp (IntermediateField.inclusion h)
  map_smul' g ξ := by ext x; rfl

/-- Original stage restriction is precomposition by the actual field inclusion. -/
def fieldFiniteGaloisFunctionsRestriction
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L') :
    ((L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) →+
      ((L' →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) where
  toFun f := f.comp (fieldFiniteGaloisEmbeddingRestriction k Ω h)
  map_zero' := by ext ξ; rfl
  map_add' f f' := by ext ξ; rfl

/-- Fix(L') is contained in Fix(L), giving the actual invariant-group inclusion. -/
def fieldFiniteGaloisInvariantsInclusion
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    {L L' : FiniteGaloisIntermediateField k Ω} (h : L ≤ L') :
    fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L →+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L' where
  toFun m := ⟨m, fun g hg => m.property g (IntermediateField.fixingSubgroup_le h hg)⟩
  map_zero' := by apply Subtype.ext; rfl
  map_add' m m' := by apply Subtype.ext; rfl

/-- EVERY original field-inclusion square commutes with original-stage evaluation. -/
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

/-- The SAME inverse-stage functions commute with EVERY actual field inclusion. -/
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

/-- The actual finite Galois field, packaged in the accepted original finite-etale basis. -/
def fieldFiniteGaloisAlgebra (L : FiniteGaloisIntermediateField k Ω) :
    (CommAlgCat.FiniteEtale.{u} k)ᵒᵖ := by
  let : Module.Finite k L := L.finiteDimensional
  have h : Etale (Spec.algebraMap k L) := (fieldFiniteGaloisEtale k Ω L).prop
  let : Algebra.Etale k L := RingHom.etale_algebraMap.mp
    ((HasRingHomProperty.Spec_iff (P := @Etale)).mp h)
  exact op (CommAlgCat.FiniteEtale.of k L)

/-- This actual finite-algebra object is the SAME original finite-Galois etale stage. -/
theorem fieldFiniteGaloisAlgebra_etale (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteEtaleToEtale k).obj (fieldFiniteGaloisAlgebra k Ω L) =
      fieldFiniteGaloisEtale k Ω L := rfl

/-- The accepted original fiber comparison sends the actual pointing to the inclusion. -/
theorem fieldFiniteGaloisAlgebra_point (L : FiniteGaloisIntermediateField k Ω) :
    fieldFiniteEtaleFiberEquiv k Ω (fieldFiniteGaloisAlgebra k Ω L)
        (fieldFiniteGaloisPoint k Ω L) = fieldFiniteGaloisEmbedding k Ω L := by
  change Spec.homEquivAlgHom (Spec.homEquivAlgHom.symm
    (IsScalarTower.toAlgHom k L Ω)) = IsScalarTower.toAlgHom k L Ω
  exact Spec.homEquivAlgHom.apply_symm_apply _


/-- The actual inverse pointing is fixed by the accepted original finite-algebra comparison. -/
theorem fieldFiniteGaloisAlgebra_point_inverse (L : FiniteGaloisIntermediateField k Ω) :
    (fieldFiniteEtaleGeometricFiberIso k Ω).inv.app (fieldFiniteGaloisAlgebra k Ω L)
        (fieldFiniteGaloisEmbedding k Ω L) = fieldFiniteGaloisPoint k Ω L := by
  change (fieldFiniteEtaleFiberEquiv k Ω (fieldFiniteGaloisAlgebra k Ω L)).symm
    (fieldFiniteGaloisEmbedding k Ω L) = fieldFiniteGaloisPoint k Ω L
  simpa only [fieldFiniteGaloisAlgebra_point] using
    (fieldFiniteEtaleFiberEquiv k Ω (fieldFiniteGaloisAlgebra k Ω L)).symm_apply_apply
      (fieldFiniteGaloisPoint k Ω L)

/-- The stage equivalence evaluates on the literal original algebra inclusion. -/
theorem fieldFiniteGaloisEvaluation_apply
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (h : (L →ₐ[k] Ω) →[Gal(Ω/k)] DiscreteAbelianAction.underlying M) :
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L h :
      DiscreteAbelianAction.underlying M) = h (fieldFiniteGaloisEmbedding k Ω L) := rfl

/-- Every extension gives the exact inverse value of the SAME additive stage equivalence. -/
theorem fieldFiniteGaloisEvaluation_symm_extension
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω)
    (m : fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L)
    (ξ : L →ₐ[k] Ω) (g : Gal(Ω/k))
    (hg : g • fieldFiniteGaloisEmbedding k Ω L = ξ) :
    (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L).symm m ξ =
      g • (m : DiscreteAbelianAction.underlying M) :=
  fieldFiniteGaloisInvariantFunction_apply_of_extension.{u, w} k Ω M L m ξ g hg

/-- The actual R(Spec L) group uses the accepted finite-algebra comparison and SAME evaluation. -/
def fieldFiniteGaloisSectionEvaluationAddEquiv
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (L : FiniteGaloisIntermediateField k Ω) :
    ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M).obj.obj
        (op (fieldFiniteGaloisEtale k Ω L)) ≃+
      fieldFiniteGaloisModuleInvariants.{u, w} k Ω M L :=
  (fieldInvariantFiniteEtaleSectionsEquiv.{u, w} k Ω M
    (fieldFiniteGaloisAlgebra k Ω L)).trans
      (fieldFiniteGaloisEvaluationAddEquiv.{u, w} k Ω M L)

/-- Original-stage evaluation is the value at its SAME original geometric pointing. -/
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

/-- The SAME inverse original section is evaluated using EVERY original fiber embedding. -/
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

/-- Every actual module map commutes with original R-stage evaluation. -/
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

/-- The actual inverse R-stage section is natural in EVERY original module morphism. -/
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

/-- Every SAME original Spec inclusion commutes with original-stage evaluation. -/
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

/-- The actual inverse-section square commutes for EVERY original field inclusion. -/
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

/-- Zero evaluation kills an actual original finite representative, hence the SAME stalk germ. -/
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

/-- The SAME constructed counit is injective on its actual original stalk carrier. -/
theorem fieldEquivariantStalkCounit_injective
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Function.Injective (DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply fieldEquivariantStalkCounit_eq_zero.{u, w} k Ω M (x - y)
  rw [map_sub, hxy, sub_self]

/-- Every actual module element has an original stage preimage under the SAME counit. -/
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

/-- Bijectivity has no finite-module or uniform finite-quotient premise. -/
theorem fieldEquivariantStalkCounit_bijective
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Function.Bijective (DiscreteAbelianAction.homToAdd
      ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)) :=
  ⟨fieldEquivariantStalkCounit_injective.{u, w} k Ω M,
    fieldEquivariantStalkCounit_surjective.{u, w} k Ω M⟩

/-- The genuine additive, equivariant, integer-linear and continuous inverse of SAME epsilon. -/
def fieldEquivariantStalkCounitIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    ((fieldGeometricStalkGaloisFunctor.{u, w} k Ω).obj
      ((fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω).obj M)) ≅ M :=
  DiscreteAbelianAction.isoOfBijective ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
    (fieldEquivariantStalkCounit_bijective.{u, w} k Ω M)

@[simp] theorem fieldEquivariantStalkCounitIso_hom
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    (fieldEquivariantStalkCounitIso.{u, w} k Ω M).hom =
      (fieldEquivariantStalkCounit.{u, w} k Ω).app M := rfl

instance fieldEquivariantStalkCounit_isIso
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    IsIso ((fieldEquivariantStalkCounit.{u, w} k Ω).app M) :=
  (fieldEquivariantStalkCounitIso.{u, w} k Ω M).isIso_hom

/-- All actual module arrows use the SAME natural evaluation isomorphism family. -/
def fieldEquivariantStalkCounitNatIso :
    fieldInvariantSkyscraperInverseSheaf.{u, w} k Ω ⋙
      fieldGeometricStalkGaloisFunctor.{u, w} k Ω ≅
        𝟭 (DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :=
  NatIso.ofComponents (fieldEquivariantStalkCounitIso.{u, w} k Ω)
    (by intro M N t; exact (fieldEquivariantStalkCounit.{u, w} k Ω).naturality t)

theorem fieldEquivariantStalkCounitNatIso_hom :
    (fieldEquivariantStalkCounitNatIso.{u, w} k Ω).hom =
      fieldEquivariantStalkCounit.{u, w} k Ω := by
  apply NatTrans.ext
  rfl

/-- The actual inverse cancels the SAME counit on every original stalk element. -/
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

/-- The SAME counit cancels its actual inverse on every possibly infinite module element. -/
theorem fieldEquivariantStalkCounit_after_inverse
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (m : DiscreteAbelianAction.underlying M) :
    DiscreteAbelianAction.homToAdd ((fieldEquivariantStalkCounit.{u, w} k Ω).app M)
      (DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m) = m := by
  have h := congrArg (fun t => DiscreteAbelianAction.homToAdd t m)
    (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv_hom_id
  simpa only [DiscreteAbelianAction.homToAdd_comp, DiscreteAbelianAction.homToAdd_id,
    AddMonoidHom.comp_apply, AddMonoidHom.id_apply, fieldEquivariantStalkCounitIso_hom] using h

/-- The inverse is the actual additive function on its original stored module carriers. -/
theorem fieldEquivariantStalkCounit_inverse_add
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k))
    (m m' : DiscreteAbelianAction.underlying M) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (m + m') =
      DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m +
        DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m' :=
  (DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv).map_add _ _

/-- Its equivariance uses the SAME original Galois automorphism and actions. -/
theorem fieldEquivariantStalkCounit_inverse_equivariant
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) (g : Gal(Ω/k))
    (m : DiscreteAbelianAction.underlying M) :
    DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv (g • m) =
      g • DiscreteAbelianAction.homToAdd (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv m :=
  DiscreteAbelianAction.homToAdd_equivariant _ g m

/-- The constructed inverse is continuous on the actual discrete source carrier. -/
theorem fieldEquivariantStalkCounit_inverse_continuous
    (M : DiscreteAbelianAction.{u, max u w} Gal(Ω/k)) :
    Continuous (DiscreteAbelianAction.homToAdd
      (fieldEquivariantStalkCounitIso.{u, w} k Ω M).inv) := continuous_of_discreteTopology

/-- EVERY original germ is the actual inverse image of its literal evaluation. -/
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

/-- EVERY invariant stage value has this actual original finite-stage inverse germ. -/
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

/-- Complete original-embedding, invariant-group and actual original-stage compatibility. -/
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

/-- The full finite-stage source laws use the constructed SAME families. -/
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

/-- The WHOLE evaluation-isomorphism source unit binds every law to SAME T, R and epsilon. -/
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

/-- The complete EVERY-module counit-isomorphism source unit, with EVERY finite stage. -/
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
