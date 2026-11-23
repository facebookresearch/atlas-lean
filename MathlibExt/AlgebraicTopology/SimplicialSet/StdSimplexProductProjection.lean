/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.StdSimplexContraction
public import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.LegacyTopCat.TopCatHomotopyEquivWeakHomotopy
import MathlibExt.AlgebraicTopology.TopologicalSpace.SimplicialRealization.PointSet.SSetRealizeHomotopy

/-!
# Standard-simplex product projections

The projection `Δ[m] ⨯ T ⟶ T` has a last-vertex section.  The standard
simplex contraction, applied in the first coordinate while the second stays
fixed, gives a simplicial homotopy from the identity to projection followed by
that section.  After realization this exhibits the projection as a homotopy
equivalence, hence as a weak homotopy equivalence.

The simplicial contraction is directed from identity to the retraction.  Its
realization is reversed only when filling the left-inverse field of the
topological homotopy equivalence.

This file makes no assertion that realization preserves products and no
Theorem A or homotopy-colimit claim.
-/

@[expose] public section

open CategoryTheory Limits CartesianMonoidalCategory
open scoped Simplicial MonoidalCategory

universe u

namespace SSet

/-- The section of `Δ[m] ⨯ T ⟶ T` at the last vertex of the standard
simplex. -/
noncomputable def stdSimplexProdLastSection (m : ℕ) (T : SSet.{u}) :
    T ⟶ (Δ[m] : SSet.{u}) ⊗ T :=
  lift
    (SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m)))
    (𝟙 T)

/-- The first projection of the last-vertex section is constant. -/
@[reassoc (attr := simp)]
theorem stdSimplexProdLastSection_fst (m : ℕ) (T : SSet.{u}) :
    stdSimplexProdLastSection m T ≫ fst _ _ =
      SSet.const (SSet.stdSimplex.obj₀Equiv.symm (Fin.last m)) :=
  lift_fst _ _

/-- The second projection of the last-vertex section is the identity. -/
@[reassoc (attr := simp)]
theorem stdSimplexProdLastSection_snd (m : ℕ) (T : SSet.{u}) :
    stdSimplexProdLastSection m T ≫ snd _ _ = 𝟙 T :=
  lift_snd _ _

/-- The standard-simplex contraction in the first coordinate of a product,
with the second coordinate fixed. -/
noncomputable def stdSimplexProdContraction (m : ℕ) (T : SSet.{u}) :
    SSet.Homotopy
      (𝟙 ((Δ[m] : SSet.{u}) ⊗ T))
      ((snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T) ≫
        stdSimplexProdLastSection m T) where
  h :=
    lift
      ((fst _ _ ▷ (Δ[1] : SSet.{u})) ≫
        (SSet.stdSimplex.homotopyIdConstLast m).h)
      (fst _ _ ≫ snd _ _)
  h₀ := by
    change SSet.ι₀ ≫ _ = 𝟙 ((Δ[m] : SSet.{u}) ⊗ T)
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, SSet.ι₀_comp_assoc,
        SSet.Homotopy.h₀, Category.comp_id, Category.id_comp]
    · simp only [Category.assoc, lift_snd, SSet.ι₀_fst_assoc,
        Category.id_comp]
  h₁ := by
    change SSet.ι₁ ≫ _ =
      (snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T) ≫
        stdSimplexProdLastSection m T
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, SSet.ι₁_comp_assoc,
        SSet.Homotopy.h₁, stdSimplexProdLastSection_fst,
        SSet.comp_const]
    · simp only [Category.assoc, lift_snd, SSet.ι₁_fst_assoc,
        stdSimplexProdLastSection_snd, Category.comp_id]
  rel := by
    ext a ⟨⟨x, hx⟩, t⟩
    all_goals
      have hx' : x ∈ (∅ : Set (((Δ[m] : SSet.{u}) ⊗ T).obj a)) := by
        simpa using hx
      have : False := (Set.mem_empty_iff_false x).mp hx'
      exact this.elim

/-- The contraction leaves the `T` coordinate fixed at every interval time. -/
@[reassoc]
theorem stdSimplexProdContraction_h_snd (m : ℕ) (T : SSet.{u}) :
    (stdSimplexProdContraction m T).h ≫ snd _ _ =
      fst _ _ ≫ snd _ _ := by
  rw [stdSimplexProdContraction]
  exact lift_snd _ _

/-- The realized projection `|Δ[m] ⨯ T| ⟶ |T|` is a homotopy
equivalence. -/
noncomputable def realizedStdSimplexProdSndHomotopyEquiv
    (m : ℕ) (T : SSet.{u}) :
    ContinuousMap.HomotopyEquiv
      (SSet.toTop.obj ((Δ[m] : SSet.{u}) ⊗ T))
      (SSet.toTop.obj T) where
  toFun :=
    (SSet.toTop.map
      (snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T)).hom
  invFun := (SSet.toTop.map (stdSimplexProdLastSection m T)).hom
  left_inv := by
    refine ⟨?_⟩
    have H := SSet.realizeHomotopy
      ((Δ[m] : SSet.{u}) ⊗ T)
      ((Δ[m] : SSet.{u}) ⊗ T)
      (𝟙 _)
      ((snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T) ≫
        stdSimplexProdLastSection m T)
      (stdSimplexProdContraction m T)
    apply ContinuousMap.Homotopy.cast H.symm
    · rw [CategoryTheory.Functor.map_comp]
      rfl
    · exact congrArg ConcreteCategory.hom
        (CategoryTheory.Functor.map_id SSet.toTop _)
  right_inv := by
    have hcomp :
        (SSet.toTop.map
            (snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T)).hom.comp
          (SSet.toTop.map (stdSimplexProdLastSection m T)).hom =
            ContinuousMap.id (SSet.toTop.obj T) := by
      rw [← TopCat.hom_comp, ← Functor.map_comp,
        stdSimplexProdLastSection_snd,
        CategoryTheory.Functor.map_id]
      exact rfl
    rw [hcomp]

/-- The forward leg of the realized product-projection homotopy equivalence is
the realized second projection. -/
@[simp]
theorem realizedStdSimplexProdSndHomotopyEquiv_toFun
    (m : ℕ) (T : SSet.{u}) :
    (realizedStdSimplexProdSndHomotopyEquiv m T).toFun =
      (SSet.toTop.map
        (snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T)).hom :=
  rfl

/-- The inverse leg is the realized last-vertex section. -/
@[simp]
theorem realizedStdSimplexProdSndHomotopyEquiv_invFun
    (m : ℕ) (T : SSet.{u}) :
    (realizedStdSimplexProdSndHomotopyEquiv m T).invFun =
      (SSet.toTop.map (stdSimplexProdLastSection m T)).hom :=
  rfl

/-- The realization of `Δ[m] ⨯ T ⟶ T` is a weak homotopy equivalence. -/
theorem stdSimplexProdSnd_mem_weakHomotopyEquivalences
    (m : ℕ) (T : SSet.{u}) :
    TopCat.weakHomotopyEquivalences
      (SSet.toTop.map
        (prod.snd : (Δ[m] : SSet.{u}) ⨯ T ⟶ T)) := by
  let e : (Δ[m] : SSet.{u}) ⊗ T ≅ (Δ[m] : SSet.{u}) ⨯ T :=
    (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _).conePointUniqueUpToIso
      (limit.isLimit (pair _ _))
  have he : e.inv ≫ snd _ _ =
      (prod.snd : (Δ[m] : SSet.{u}) ⨯ T ⟶ T) := by
    exact IsLimit.conePointUniqueUpToIso_inv_comp
      (CartesianMonoidalCategory.tensorProductIsBinaryProduct _ _)
      (limit.isLimit (pair _ _)) ⟨WalkingPair.right⟩
  have h := MorphismProperty.RespectsIso.precomp
    TopCat.weakHomotopyEquivalences
    (SSet.toTop.map e.inv)
    (SSet.toTop.map
      (snd _ _ : (Δ[m] : SSet.{u}) ⊗ T ⟶ T))
    (TopCat.mem_of_eq_toFun
      (realizedStdSimplexProdSndHomotopyEquiv m T) rfl)
  simpa only [← Functor.map_comp, he] using h

end SSet

end
