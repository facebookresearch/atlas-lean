/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.AlgebraicTopology.SimplicialObject.CosimplicialCupAssociativity
public import MathlibExt.Algebra.Category.Grp.MonoidalPreadditive
public import MathlibExt.Algebra.Homology.GradedPairingHomology
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Monoidal.Limits.Colimits

/-!
## # Coface comparisons, alternating complexes and conditional AW pairing transport
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe uC vC uD vD uE vE s
open CategoryTheory CategoryTheory.Limits AlgebraicTopology

open MonoidalCategory
open scoped BigOperators TensorProduct

namespace AlgebraicTopology.CosimplicialCup

variable {C : Type uC} [Category.{vC} C]

/--
A comparison in every degree with the coface squares. Codegeneracy compatibility is not needed for
the alternating complex or AW cup.
-/
structure CofaceComparison (A B : CosimplicialObject C) where
  /-- The comparison morphism in degree `n`. -/
  app (n : ℕ) : A.obj (SimplexCategory.mk n) ⟶ B.obj (SimplexCategory.mk n)
  /-- Every original coface commutes with the comparison. -/
  coface (n : ℕ) (i : Fin (n + 2)) :
    A.δ i ≫ app (n + 1) = app n ≫ B.δ i

set_option backward.isDefEq.respectTransparency.types false in
/-- The coface squares imply naturality for every injective simplex map. -/
theorem CofaceComparison.naturality_mono {A B : CosimplicialObject C}
    (e : CofaceComparison A B) {x y : SimplexCategory} (f : x ⟶ y) [Mono f] :
    A.map f ≫ e.app y.len = e.app x.len ≫ B.map f := by
  let P : MorphismProperty SimplexCategory :=
    fun x y f => A.map f ≫ e.app y.len = e.app x.len ≫ B.map f
  apply SimplexCategory.mono_induction (motive := P) ?_ ?_ f
  · intro x
    dsimp only [P]
    simp only [A.map_id, B.map_id, Category.id_comp, Category.comp_id]
  · intro x y f i hf
    dsimp only [P] at hf ⊢
    have hδ : A.map (SimplexCategory.δ i) ≫ e.app (y.len + 1) =
        e.app y.len ≫ B.map (SimplexCategory.δ i) := e.coface y.len i
    simp only [Functor.map_comp]
    rw [Category.assoc, hδ, ← Category.assoc, hf, Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- The same coface comparison gives the alternating-cochain map. -/
def CofaceComparison.alternatingMap [Preadditive C] {A B : CosimplicialObject C}
    (e : CofaceComparison A B) :
    AlternatingCofaceMapComplex.obj A ⟶ AlternatingCofaceMapComplex.obj B :=
  CochainComplex.ofHom e.app fun n => by
    dsimp only [AlternatingCofaceMapComplex.obj]
    rw [CochainComplex.of_d, CochainComplex.of_d]
    change e.app n ≫ (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • B.δ i) =
      (∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val • A.δ i) ≫ e.app (n + 1)
    rw [Preadditive.comp_sum, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro i _
    rw [Preadditive.comp_zsmul, Preadditive.zsmul_comp, e.coface n i]

private theorem frontMono (p q n : ℕ) (h : p + q = n) :
    Mono (AlexanderWhitney.frontInclusion p q n h) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simpa only [AlexanderWhitney.frontInclusion_toOrderHom] using hv

private theorem backMono (p q n : ℕ) (h : p + q = n) :
    Mono (AlexanderWhitney.backInclusion p q n h) := by
  apply SimplexCategory.mono_iff_injective.mpr
  intro i j hij
  apply Fin.ext
  have hv := congrArg Fin.val hij
  simp only [AlexanderWhitney.backInclusion_toOrderHom] at hv
  omega

set_option backward.isDefEq.respectTransparency.types false in
/--
Literal front/back AW pairing naturality follows from the coface maps and the degreewise tensor
square.
-/
theorem awPair_cofaceComparison [MonoidalCategory C]
    {A A' B B' D D' : CosimplicialObject C}
    (a : CofaceComparison A A') (b : CofaceComparison B B')
    (c : CofaceComparison D D')
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n))
    (m' : ∀ n, A'.obj (SimplexCategory.mk n) ⊗ B'.obj (SimplexCategory.mk n) ⟶
      D'.obj (SimplexCategory.mk n))
    (hm : ∀ n, (a.app n ⊗ₘ b.app n) ≫ m' n = m n ≫ c.app n)
    (p q n : ℕ) (h : p + q = n) :
    (a.app p ⊗ₘ b.app q) ≫ awPair A' B' D' m' p q n h =
      awPair A B D m p q n h ≫ c.app n := by
  let f := AlexanderWhitney.frontInclusion p q n h
  let g := AlexanderWhitney.backInclusion p q n h
  let : Mono f := frontMono p q n h
  let : Mono g := backMono p q n h
  have ha := a.naturality_mono f
  have hb := b.naturality_mono g
  unfold awPair
  rw [← Category.assoc, tensorHom_comp_tensorHom, ← ha, ← hb,
    ← tensorHom_comp_tensorHom, Category.assoc, hm n, ← Category.assoc]

/-- Coface-compatible degree isomorphisms. -/
structure CofaceIso (A B : CosimplicialObject C) where
  /-- The coefficient isomorphism in degree `n`. -/
  app (n : ℕ) : A.obj (SimplexCategory.mk n) ≅ B.obj (SimplexCategory.mk n)
  /-- The forward isomorphisms commute with every original coface. -/
  coface (n : ℕ) (i : Fin (n + 2)) :
    A.δ i ≫ (app (n + 1)).hom = (app n).hom ≫ B.δ i

/-- The forward comparison retains the given degree isomorphisms literally. -/
def CofaceIso.homComparison {A B : CosimplicialObject C} (e : CofaceIso A B) :
    CofaceComparison A B := ⟨fun n => (e.app n).hom, e.coface⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- The inverse degree isomorphisms also commute with the cofaces. -/
def CofaceIso.invComparison {A B : CosimplicialObject C} (e : CofaceIso A B) :
    CofaceComparison B A where
  app n := (e.app n).inv
  coface n i := by
    rw [← cancel_mono (e.app (n + 1)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [e.coface n i]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The literal degree isomorphisms form an isomorphism of alternating complexes. -/
def CofaceIso.alternatingIso [Preadditive C] {A B : CosimplicialObject C}
    (e : CofaceIso A B) :
    AlternatingCofaceMapComplex.obj A ≅ AlternatingCofaceMapComplex.obj B where
  hom := e.homComparison.alternatingMap
  inv := e.invComparison.alternatingMap
  hom_inv_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (e.app n).hom ≫ (e.app n).inv = 𝟙 _
    exact (e.app n).hom_inv_id
  inv_hom_id := by
    apply HomologicalComplex.Hom.ext
    funext n
    change (e.app n).inv ≫ (e.app n).hom = 𝟙 _
    exact (e.app n).inv_hom_id

section Homology

variable {A A' B B' D D' : CosimplicialObject AddCommGrpCat.{s}}

set_option backward.isDefEq.respectTransparency.types false in
/--
The original homology pairings commute under the coface comparison. The pairing components are
supplied by their literal front/back definitions; the cochain or cohomology naturality law is
proved here.
-/
theorem pairHomology_cofaceComparison
    (a : CofaceComparison A A') (b : CofaceComparison B B')
    (c : CofaceComparison D D')
    (P : HomologicalComplex.CochainGradedPairing
      (AlternatingCofaceMapComplex.obj A) (AlternatingCofaceMapComplex.obj B)
      (AlternatingCofaceMapComplex.obj D))
    (Q : HomologicalComplex.CochainGradedPairing
      (AlternatingCofaceMapComplex.obj A') (AlternatingCofaceMapComplex.obj B')
      (AlternatingCofaceMapComplex.obj D'))
    (m : ∀ n, A.obj (SimplexCategory.mk n) ⊗ B.obj (SimplexCategory.mk n) ⟶
      D.obj (SimplexCategory.mk n))
    (m' : ∀ n, A'.obj (SimplexCategory.mk n) ⊗ B'.obj (SimplexCategory.mk n) ⟶
      D'.obj (SimplexCategory.mk n))
    (hP : ∀ p q, P.pair p q = awPair A B D m p q (p + q) rfl)
    (hQ : ∀ p q, Q.pair p q = awPair A' B' D' m' p q (p + q) rfl)
    (hm : ∀ n, (a.app n ⊗ₘ b.app n) ≫ m' n = m n ≫ c.app n)
    (p q : ℕ) :
    (HomologicalComplex.homologyMap a.alternatingMap p ⊗ₘ
        HomologicalComplex.homologyMap b.alternatingMap q) ≫ Q.pairHomology p q =
      P.pairHomology p q ≫
        HomologicalComplex.homologyMap c.alternatingMap (p + q) := by
  apply HomologicalComplex.CochainGradedPairing.pairHomology_naturality P Q
    a.alternatingMap b.alternatingMap c.alternatingMap
  intro i j
  change P.pair i j ≫ c.app (i + j) = (a.app i ⊗ₘ b.app j) ≫ Q.pair i j
  rw [hP i j, hQ i j]
  exact (awPair_cofaceComparison a b c m m' hm i j (i + j) rfl).symm

end Homology

set_option backward.isDefEq.respectTransparency.types false in
/--
An functor comparison carries literal coface isomorphisms through the two functors, retaining
their component maps.
-/
def cofaceIsoWhiskerNatIso {C : Type uC} [Category.{vC} C]
    {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
    (A : CosimplicialObject C) (B : CosimplicialObject D) (J : C ⥤ D)
    (Γ : C ⥤ E) (I : D ⥤ E) (g : Γ ≅ J ⋙ I)
    (a : CosimplicialCup.CofaceIso (A ⋙ J) B) :
    CosimplicialCup.CofaceIso (A ⋙ Γ) (B ⋙ I) where
  app n := g.app (A.obj (SimplexCategory.mk n)) ≪≫ I.mapIso (a.app n)
  coface n i := by
    have hg : Γ.map (A.δ i) ≫ g.hom.app (A.obj (SimplexCategory.mk (n + 1))) =
        g.hom.app (A.obj (SimplexCategory.mk n)) ≫ I.map (J.map (A.δ i)) :=
      g.hom.naturality (A.δ i)
    have ha : J.map (A.δ i) ≫ (a.app (n + 1)).hom = (a.app n).hom ≫ B.δ i :=
      a.coface n i
    change Γ.map (A.δ i) ≫
        (g.hom.app (A.obj (SimplexCategory.mk (n + 1))) ≫ I.map (a.app (n + 1)).hom) =
      (g.hom.app (A.obj (SimplexCategory.mk n)) ≫ I.map (a.app n).hom) ≫ I.map (B.δ i)
    rw [← Category.assoc, hg, Category.assoc, ← I.map_comp, ha,
      I.map_comp, ← Category.assoc]

end AlgebraicTopology.CosimplicialCup
