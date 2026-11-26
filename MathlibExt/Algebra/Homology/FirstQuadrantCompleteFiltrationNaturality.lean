/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantCompleteFiltration
public import MathlibExt.Algebra.Homology.FirstQuadrantFiltrationNaturality

/-!
# Naturality of complete horizontal filtration stages

Let C be preadditive with a zero object and finite coproducts. A morphism f:K→L of bicomplexes
of shape (down ℕ,down ℕ) induces a chain map G_i(f):G_i(K)→G_i(L) for every cut i∈ℤ∪{⊥,⊤} of the
complete horizontal filtration. This map is zero at bottom and negative finite cuts, the finite
horizontal-stage map at each nonnegative integer cut, and Tot f at top.

If ι_i^K:G_i(K)→Tot K denotes the stage inclusion, then G_i(f)≫ι_i^L=ι_i^K≫Tot f. For i≤j, the
complete transitions satisfy G_i(f)≫t^L_{i,j}=t^K_{i,j}≫G_j(f). These stage maps therefore
define a morphism between the completely filtered total complexes, with arbitrary object and
morphism universes.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
variable {K L : HomologicalComplex₂ C (ComplexShape.down ℕ)
  (ComplexShape.down ℕ)}

/-- Let C be preadditive with a zero object and finite coproducts, f:K→L a morphism of
first-quadrant bicomplexes, and i∈ℤ∪{⊥,⊤}. This is the pair consisting of the induced chain map
G_i(f):G_i(K)→G_i(L) and the equality G_i(f)≫ι_i^L=ι_i^K≫Tot f. The map is zero at bottom or
negative finite cuts, the finite horizontal-stage map at a≥0, and the total map at top. -/
noncomputable def horizontalCompleteFilteredTotalComplexMapOfBicomplexData
    (f : K ⟶ L) (i : EInt) :
    { g : horizontalCompleteFilteredTotalComplex K i ⟶
        horizontalCompleteFilteredTotalComplex L i //
      g ≫ horizontalCompleteFilteredTotalToTotal L i =
        horizontalCompleteFilteredTotalToTotal K i ≫
          total.map f (ComplexShape.down ℕ) } := by
  induction i using WithBotTop.rec with
  | bot =>
      refine ⟨0, ?_⟩
      change (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
          (HomologicalComplex.zero : ChainComplex C ℕ)) ≫ 0 =
        0 ≫ total.map f (ComplexShape.down ℕ)
      simp
  | coe a =>
      by_cases ha : 0 ≤ a
      · simp only [horizontalCompleteFilteredTotalComplex,
          horizontalCompleteFilteredTotalToTotal,
          horizontalCompleteFilteredTotalMonoOver,
          WithBotTop.rec_coe]
        rw [ite_eq_left ha, ite_eq_left ha]
        refine ⟨horizontalFilteredTotalComplexMapOfBicomplex f a.toNat, ?_⟩
        change horizontalFilteredTotalComplexMapOfBicomplex f a.toNat ≫
            horizontalFilteredTotalComplexToTotal L a.toNat =
          horizontalFilteredTotalComplexToTotal K a.toNat ≫
            total.map f (ComplexShape.down ℕ)
        exact horizontalFilteredTotalComplexMapOfBicomplex_toTotal
          f a.toNat
      · simp only [horizontalCompleteFilteredTotalComplex,
          horizontalCompleteFilteredTotalToTotal,
          horizontalCompleteFilteredTotalMonoOver,
          WithBotTop.rec_coe]
        rw [ite_eq_right ha, ite_eq_right ha]
        refine ⟨0, ?_⟩
        change (0 : (HomologicalComplex.zero : ChainComplex C ℕ) ⟶
            (HomologicalComplex.zero : ChainComplex C ℕ)) ≫ 0 =
          0 ≫ total.map f (ComplexShape.down ℕ)
        simp
  | top =>
      simp only [horizontalCompleteFilteredTotalComplex,
        horizontalCompleteFilteredTotalToTotal,
        horizontalCompleteFilteredTotalMonoOver,
        WithBotTop.rec_top]
      refine ⟨total.map f (ComplexShape.down ℕ), ?_⟩
      change total.map f (ComplexShape.down ℕ) ≫ 𝟙 _ =
        𝟙 _ ≫ total.map f (ComplexShape.down ℕ)
      simp

/-- For a morphism f:K→L of bicomplexes of shape (down ℕ,down ℕ) in a preadditive category with a
zero object and finite coproducts, and a cut i∈ℤ∪{⊥,⊤}, this is the induced chain map
G_i(f):G_i(K)→G_i(L). It is the zero map at bottom and negative finite cuts, the finite
horizontal-stage map at nonnegative integer cuts, and Tot f at top. -/
noncomputable def horizontalCompleteFilteredTotalComplexMapOfBicomplex
    (f : K ⟶ L) (i : EInt) :
    horizontalCompleteFilteredTotalComplex K i ⟶
      horizontalCompleteFilteredTotalComplex L i :=
  (horizontalCompleteFilteredTotalComplexMapOfBicomplexData f i).1

/-- Let C be preadditive with a zero object and finite coproducts, f:K→L a first-quadrant bicomplex
morphism, and i∈ℤ∪{⊥,⊤}. With G_i(f) the induced complete-stage chain map and ι_i^K:G_i(K)→Tot
K, ι_i^L:G_i(L)→Tot L the inclusions, G_i(f)≫ι_i^L=ι_i^K≫Tot f. -/
@[reassoc (attr := simp)]
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal
    (f : K ⟶ L) (i : EInt) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalToTotal L i =
      horizontalCompleteFilteredTotalToTotal K i ≫
        total.map f (ComplexShape.down ℕ) :=
  (horizontalCompleteFilteredTotalComplexMapOfBicomplexData f i).2

/-- For a first-quadrant bicomplex morphism f:K→L in a preadditive category with a zero object and
finite coproducts, let i≤j in ℤ∪{⊥,⊤}. The complete-stage maps and transitions satisfy
G_i(f)≫t^L_{i,j}=t^K_{i,j}≫G_j(f), as maps G_i(K)→G_j(L). The equality includes zero bottom and
negative stages and the top total complex. -/
theorem horizontalCompleteFilteredTotalComplexMapOfBicomplex_naturality
    (f : K ⟶ L) {i j : EInt} (h : i ≤ j) :
    horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalMap L h =
      horizontalCompleteFilteredTotalMap K h ≫
        horizontalCompleteFilteredTotalComplexMapOfBicomplex f j := by
  apply (cancel_mono
    (horizontalCompleteFilteredTotalToTotal L j)).1
  calc
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
          horizontalCompleteFilteredTotalMap L h) ≫
        horizontalCompleteFilteredTotalToTotal L j =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        (horizontalCompleteFilteredTotalMap L h ≫
          horizontalCompleteFilteredTotalToTotal L j) :=
      Category.assoc _ _ _
    _ = horizontalCompleteFilteredTotalComplexMapOfBicomplex f i ≫
        horizontalCompleteFilteredTotalToTotal L i := by
      rw [horizontalCompleteFilteredTotalMap_toTotal]
    _ = horizontalCompleteFilteredTotalToTotal K i ≫
        total.map f (ComplexShape.down ℕ) :=
      horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f i
    _ = (horizontalCompleteFilteredTotalMap K h ≫
          horizontalCompleteFilteredTotalToTotal K j) ≫
        total.map f (ComplexShape.down ℕ) := by
      rw [horizontalCompleteFilteredTotalMap_toTotal]
    _ = horizontalCompleteFilteredTotalMap K h ≫
        (horizontalCompleteFilteredTotalToTotal K j ≫
          total.map f (ComplexShape.down ℕ)) :=
      Category.assoc _ _ _
    _ = horizontalCompleteFilteredTotalMap K h ≫
        (horizontalCompleteFilteredTotalComplexMapOfBicomplex f j ≫
          horizontalCompleteFilteredTotalToTotal L j) := by
      rw [horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal]
    _ = (horizontalCompleteFilteredTotalMap K h ≫
          horizontalCompleteFilteredTotalComplexMapOfBicomplex f j) ≫
        horizontalCompleteFilteredTotalToTotal L j :=
      (Category.assoc _ _ _).symm

/-- Let C be preadditive with a zero object and finite coproducts and K a bicomplex of shape (down
ℕ,down ℕ). This filtered object consists of the chain complex Tot K and its increasing
horizontal filtration indexed by ℤ∪{⊥,⊤}. Bottom and negative finite stages are zero, the
nonnegative finite stage a is G^fin_a(K), and the top stage is Tot K; all stages have their
canonical monic inclusions into Tot K. -/
noncomputable def horizontalCompleteTotalFilteredObject
    (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
      (ComplexShape.down ℕ)) :
    CategoryTheory.FilteredObject (ChainComplex C ℕ) EInt where
  X := K.total (ComplexShape.down ℕ)
  filtration := horizontalCompleteTotalFiltration K

/-- For a morphism f:K→L of first-quadrant bicomplexes in a preadditive category with a zero object
and finite coproducts, this filtered-object morphism has underlying chain map Tot f and stage
components G_i(f):G_i(K)→G_i(L) for i∈ℤ∪{⊥,⊤}. The stage maps commute with transitions and
satisfy G_i(f)≫ι_i^L=ι_i^K≫Tot f, so they preserve the complete horizontal filtrations. -/
noncomputable def horizontalCompleteTotalFilteredObjectMap (f : K ⟶ L) :
    horizontalCompleteTotalFilteredObject K ⟶
      horizontalCompleteTotalFilteredObject L :=
  CategoryTheory.FilteredObject.homMk
    (total.map f (ComplexShape.down ℕ))
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex f)
    (horizontalCompleteFilteredTotalComplexMapOfBicomplex_toTotal f)

@[simp]
theorem horizontalCompleteTotalFilteredObjectMap_hom (f : K ⟶ L) :
    (horizontalCompleteTotalFilteredObjectMap f).hom =
      total.map f (ComplexShape.down ℕ) :=
  rfl

@[simp]
theorem horizontalCompleteTotalFilteredObjectMap_natTrans_app
    (f : K ⟶ L) (i : EInt) :
    (horizontalCompleteTotalFilteredObjectMap f).natTrans.app i =
      horizontalCompleteFilteredTotalComplexMapOfBicomplex f i :=
  rfl

end HomologicalComplex₂

end
