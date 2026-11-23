/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationCompactSupport
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationPath

/-!
# Compact maps into simplicial realizations factor through finite subcomplexes

Every map from a compact `TopCat` object into a simplicial realization factors
through the realization of a finite subcomplex.  If a chosen source point maps
to a realized vertex, the support can be enlarged by that vertex and the lift
preserves the basepoint literally.

These results provide only compact finite support.  They make no simplicial
approximation, nullhomotopy, homotopy-group, or weak-equivalence claim.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Topology
open scoped Simplicial

universe u

namespace SSet

private theorem finite_sup_subcomplex_for_factor {X : SSet.{u}}
    (S T : X.Subcomplex)
    (hS : SSet.Finite (S : SSet.{u}))
    (hT : SSet.Finite (T : SSet.{u})) :
    SSet.Finite ((S ⊔ T : X.Subcomplex) : SSet.{u}) := by
  let F : Bool → X.Subcomplex := fun b => cond b T S
  have hST : (S ⊔ T : X.Subcomplex) = ⨆ b, F b := by
    apply le_antisymm
    · exact sup_le (by simpa [F] using le_iSup F false)
        (by simpa [F] using le_iSup F true)
    · apply iSup_le
      intro b
      cases b <;> simp [F]
  have hfin : SSet.Finite ((⨆ b, F b : X.Subcomplex) : SSet.{u}) := by
    rw [SSet.finite_iSup_iff]
    intro b
    cases b
    · simpa [F] using hS
    · simpa [F] using hT
  rwa [← hST] at hfin

/-- A map from a compact space into a simplicial realization factors through
one finite subcomplex. -/
theorem exists_finite_subcomplex_factor_topCatHom
    {X : SSet.{u}} {K : TopCat.{u}} [CompactSpace K]
    (f : K ⟶ SSet.toTop.obj X) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      f = g ≫ SSet.toTop.map A.ι := by
  classical
  have hcompact : IsCompact (Set.range f) :=
    isCompact_range f.hom.continuous
  obtain ⟨A, hA, hsub⟩ :=
    SSet.exists_finite_subcomplex_of_isCompact X (Set.range f) hcompact
  let e : SSet.toTop.obj (A : SSet.{u}) ⟶ SSet.toTop.obj X :=
    SSet.toTop.map A.ι
  have he : IsEmbedding e :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := A)).isEmbedding
  let fr : C(K, Set.range e) :=
    ⟨fun z => ⟨f z, hsub ⟨z, rfl⟩⟩,
      f.hom.continuous.subtype_mk _⟩
  let hInv : C(Set.range e, SSet.toTop.obj (A : SSet.{u})) :=
    ⟨he.toHomeomorph.symm, he.toHomeomorph.symm.continuous⟩
  let g : K ⟶ SSet.toTop.obj (A : SSet.{u}) :=
    TopCat.ofHom (hInv.comp fr)
  refine ⟨A, hA, g, ?_⟩
  ext z
  have hz := he.toHomeomorph.apply_symm_apply (fr z)
  change (fr z).val = e (he.toHomeomorph.symm (fr z))
  exact (congrArg Subtype.val hz).symm

/-- A based map from a compact space factors through a finite subcomplex
containing the chosen simplicial vertex, with the lifted basepoint literal. -/
theorem exists_finite_subcomplex_factor_topCatHom_at_realizedVertex
    {X : SSet.{u}} (x : X _⦋0⦌)
    {K : TopCat.{u}} [CompactSpace K] (k : K)
    (f : K ⟶ SSet.toTop.obj X)
    (hk : f k = SSet.realizedVertex x) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hx : x ∈ A.obj (op ⦋0⦌))
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      g k = SSet.realizedVertex
          (⟨x, hx⟩ : (A : SSet.{u}) _⦋0⦌) ∧
        f = g ≫ SSet.toTop.map A.ι := by
  classical
  obtain ⟨A₀, hA₀, g₀, hg₀⟩ :=
    SSet.exists_finite_subcomplex_factor_topCatHom f
  let A : X.Subcomplex := A₀ ⊔ SSet.Subcomplex.ofSimplex x
  have hA : SSet.Finite (A : SSet.{u}) :=
    finite_sup_subcomplex_for_factor A₀ (SSet.Subcomplex.ofSimplex x) hA₀
      (SSet.Subcomplex.finite_ofSimplex X x)
  have hx : x ∈ A.obj (op ⦋0⦌) :=
    (show SSet.Subcomplex.ofSimplex x ≤ A from le_sup_right)
      _ (SSet.Subcomplex.mem_ofSimplex_obj x)
  let j : (A₀ : SSet.{u}) ⟶ (A : SSet.{u}) :=
    SSet.Subcomplex.homOfLE le_sup_left
  let g : K ⟶ SSet.toTop.obj (A : SSet.{u}) :=
    g₀ ≫ SSet.toTop.map j
  have hfac : f = g ≫ SSet.toTop.map A.ι := by
    rw [hg₀]
    change g₀ ≫ SSet.toTop.map A₀.ι =
      (g₀ ≫ SSet.toTop.map j) ≫ SSet.toTop.map A.ι
    rw [Category.assoc, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  have he : Function.Injective (SSet.toTop.map A.ι) :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := A)).isEmbedding.injective
  let xA : (A : SSet.{u}) _⦋0⦌ := ⟨x, hx⟩
  have hvertex : SSet.realizedVertex x =
      SSet.toTop.map A.ι (SSet.realizedVertex xA) :=
    SSet.realizedVertex_naturality A.ι xA
  have hgk : g k = SSet.realizedVertex xA := by
    apply he
    calc
      SSet.toTop.map A.ι (g k) = f k :=
        (ConcreteCategory.congr_hom hfac k).symm
      _ = SSet.realizedVertex x := hk
      _ = SSet.toTop.map A.ι (SSet.realizedVertex xA) := hvertex
  exact ⟨A, hA, hx, g, hgk, hfac⟩

end SSet

end
