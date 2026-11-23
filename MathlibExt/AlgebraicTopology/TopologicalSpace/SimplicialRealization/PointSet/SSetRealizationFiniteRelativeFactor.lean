/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizationFiniteFactor

/-!
# Finite factorization retaining a prescribed subcomplex

A compact map into a simplicial realization factors through a finite
subcomplex while retaining an exact prescribed restriction through another
finite subcomplex. A set-level wrapper constructs the prescribed lift from a
`MapsTo` hypothesis using the realized inclusion's embedding homeomorphism.

No global choice, simplicial approximation, nonsingularity, homotopy-group,
or weak-equivalence statement is introduced.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Topology
open scoped Simplicial

universe u

namespace SSet

private theorem finite_sup_subcomplex_relative {X : SSet.{u}}
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

/-- A compact map factors through a finite subcomplex while retaining an
exact specified restriction through a prescribed finite subcomplex. -/
theorem exists_finite_subcomplex_factor_topCatHom_of_restriction
    {X : SSet.{u}} {K L : TopCat.{u}} [CompactSpace K]
    (B : X.Subcomplex) (hB : SSet.Finite (B : SSet.{u}))
    (i : L ⟶ K)
    (b : L ⟶ SSet.toTop.obj (B : SSet.{u}))
    (f : K ⟶ SSet.toTop.obj X)
    (hrestrict : i ≫ f = b ≫ SSet.toTop.map B.ι) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      i ≫ g =
          b ≫ SSet.toTop.map (SSet.Subcomplex.homOfLE hBA) ∧
        f = g ≫ SSet.toTop.map A.ι := by
  classical
  obtain ⟨A₀, hA₀, g₀, hg₀⟩ :=
    SSet.exists_finite_subcomplex_factor_topCatHom f
  let A : X.Subcomplex := A₀ ⊔ B
  have hA : SSet.Finite (A : SSet.{u}) :=
    finite_sup_subcomplex_relative A₀ B hA₀ hB
  have hBA : B ≤ A := le_sup_right
  let j₀ : (A₀ : SSet.{u}) ⟶ (A : SSet.{u}) :=
    SSet.Subcomplex.homOfLE le_sup_left
  let jB : (B : SSet.{u}) ⟶ (A : SSet.{u}) :=
    SSet.Subcomplex.homOfLE hBA
  let g : K ⟶ SSet.toTop.obj (A : SSet.{u}) :=
    g₀ ≫ SSet.toTop.map j₀
  have hfac : f = g ≫ SSet.toTop.map A.ι := by
    rw [hg₀]
    change g₀ ≫ SSet.toTop.map A₀.ι =
      (g₀ ≫ SSet.toTop.map j₀) ≫ SSet.toTop.map A.ι
    rw [Category.assoc, ← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  have he : Function.Injective (SSet.toTop.map A.ι) :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := A)).isEmbedding.injective
  have hmapB :
      SSet.toTop.map jB ≫ SSet.toTop.map A.ι =
        SSet.toTop.map B.ι := by
    rw [← Functor.map_comp, SSet.Subcomplex.homOfLE_ι]
  have hrestrict' :
      i ≫ g = b ≫ SSet.toTop.map jB := by
    apply ConcreteCategory.hom_ext
    intro z
    apply he
    calc
      SSet.toTop.map A.ι ((i ≫ g) z) = f (i z) := by
        simpa only [CategoryTheory.comp_apply] using
          (ConcreteCategory.congr_hom hfac (i z)).symm
      _ = SSet.toTop.map B.ι (b z) := by
        simpa only [CategoryTheory.comp_apply] using
          ConcreteCategory.congr_hom hrestrict z
      _ = SSet.toTop.map A.ι
          ((b ≫ SSet.toTop.map jB) z) := by
        simpa only [CategoryTheory.comp_apply] using
          (ConcreteCategory.congr_hom hmapB (b z)).symm
  exact ⟨A, hA, hBA, g, hrestrict', hfac⟩

/-- A compact map whose prescribed set lands in a finite subcomplex factors
through a finite enlargement, with the lifted set still landing in the
realized prescribed subcomplex. -/
theorem exists_finite_subcomplex_factor_topCatHom_of_mapsTo
    {X : SSet.{u}} {K : TopCat.{u}} [CompactSpace K]
    (B : X.Subcomplex) (hB : SSet.Finite (B : SSet.{u}))
    (S : Set K)
    (f : K ⟶ SSet.toTop.obj X)
    (hS : Set.MapsTo f S (Set.range (SSet.toTop.map B.ι))) :
    ∃ (A : X.Subcomplex) (_ : SSet.Finite (A : SSet.{u}))
      (hBA : B ≤ A)
      (g : K ⟶ SSet.toTop.obj (A : SSet.{u})),
      Set.MapsTo g S
          (Set.range
            (SSet.toTop.map (SSet.Subcomplex.homOfLE hBA))) ∧
        f = g ≫ SSet.toTop.map A.ι := by
  classical
  let eB : SSet.toTop.obj (B : SSet.{u}) ⟶ SSet.toTop.obj X :=
    SSet.toTop.map B.ι
  have heB : IsEmbedding eB :=
    (SSet.Subcomplex.closedT1Embeddings_toTop_map_ι (S := B)).isEmbedding
  let i : TopCat.of S ⟶ K :=
    TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  let fr : C(S, Set.range eB) :=
    ⟨fun z => ⟨f z, hS z.property⟩,
      (f.hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  let hInv : C(Set.range eB, SSet.toTop.obj (B : SSet.{u})) :=
    ⟨heB.toHomeomorph.symm, heB.toHomeomorph.symm.continuous⟩
  let b : TopCat.of S ⟶ SSet.toTop.obj (B : SSet.{u}) :=
    TopCat.ofHom (hInv.comp fr)
  have hrestrict : i ≫ f = b ≫ eB := by
    apply ConcreteCategory.hom_ext
    intro z
    have hz := heB.toHomeomorph.apply_symm_apply (fr z)
    change (fr z).val = eB (heB.toHomeomorph.symm (fr z))
    exact (congrArg Subtype.val hz).symm
  obtain ⟨A, hA, hBA, g, hrestrict', hfac⟩ :=
    SSet.exists_finite_subcomplex_factor_topCatHom_of_restriction
      B hB i b f hrestrict
  refine ⟨A, hA, hBA, g, ?_, hfac⟩
  intro z hz
  let zS : S := ⟨z, hz⟩
  refine ⟨b zS, ?_⟩
  have hzrestrict := ConcreteCategory.congr_hom hrestrict' zS
  have hiz : i zS = z := rfl
  simpa only [CategoryTheory.comp_apply, hiz] using hzrestrict.symm

end SSet
