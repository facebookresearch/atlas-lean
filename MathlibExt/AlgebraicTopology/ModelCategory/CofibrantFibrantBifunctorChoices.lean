/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import Mathlib.CategoryTheory.Localization.Bifunctor

/-!
# Coherent comparison of cofibrant-source and fibrant-target choices

The same bifunctor is evaluated at two caller supplied Q/R records. Its
homotopicality on cofibrant/fibrant pairs gives a common comparison using
the actual Q counits and R units. These comparisons preserve the ordinary
map and therefore satisfy identity, composition and uniqueness on the
entire source category.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe uS vS uT vT uE vE

open CategoryTheory CategoryTheory.MorphismProperty Opposite Functor
open scoped CategoryTheory.Prod

namespace HomotopicalAlgebra.CofibrantFibrantBifunctorChoices

variable {S : Type uS} [Category.{vS} S] [ModelCategory S]
  {T : Type uT} [Category.{vT} T] [ModelCategory T]
  {E : Type uE} [Category.{vE} E]
  (F : Sᵒᵖ × T ⥤ E)
  (q p : GeneratedFunctorialReplacements.Data (C := S))
  (r s : GeneratedFunctorialReplacements.Data (C := T))

/-- Homotopicality is required only at the actual cofibrant/fibrant endpoints. -/
def OnCofibrantFibrant : Prop :=
  ∀ {N N' : S} {X X' : T} (f : N' ⟶ N) (g : X ⟶ X'),
    IsCofibrant N → IsCofibrant N' → IsFibrant X → IsFibrant X' →
      weakEquivalences S f → weakEquivalences T g →
        IsIso (F.map ((f.op, g) : (op N, X) ⟶ (op N', X')))

/-- Replacement changes the arguments of the original bifunctor. -/
def raw : Sᵒᵖ × T ⥤ E := (q.Q.op.prod r.R) ⋙ F

/-- The source counit and target unit give the ordinary comparison. -/
def ordinaryMap : F ⟶ raw F q r :=
  whiskerRight (NatTrans.prod (NatTrans.op q.q) r.r) F

/-- The actual outer Q gives a common cofibrant source. -/
def commonQ : S ⥤ S := p.Q ⋙ q.Q

/-- The actual outer R gives a common fibrant target. -/
def commonR : T ⥤ T := s.R ⋙ r.R

/-- The first source comparison applies the original Q to the other counit. -/
def firstQMap : commonQ q p ⟶ q.Q :=
  whiskerRight p.q q.Q ≫ q.Q.leftUnitor.hom

/-- The second source comparison is the original outer Q counit. -/
def secondQMap : commonQ q p ⟶ p.Q :=
  whiskerLeft p.Q q.q ≫ p.Q.rightUnitor.hom

/-- The first target comparison applies the original R to the other unit. -/
def firstRMap : r.R ⟶ commonR r s :=
  r.R.leftUnitor.inv ≫ whiskerRight s.r r.R

/-- The second target comparison is the original outer R unit. -/
def secondRMap : s.R ⟶ commonR r s :=
  s.R.rightUnitor.inv ≫ whiskerLeft s.R r.r

/-- Both choices use one actual common bifunctor. -/
def common : Sᵒᵖ × T ⥤ E := ((commonQ q p).op.prod (commonR r s)) ⋙ F

/-- Source precomposition and target postcomposition are one natural transformation. -/
def map {Q Q' : S ⥤ S} {R R' : T ⥤ T} (a : Q' ⟶ Q) (b : R ⟶ R') :
    (Q.op.prod R) ⋙ F ⟶ (Q'.op.prod R') ⋙ F :=
  whiskerRight (NatTrans.prod (NatTrans.op a) b) F

/-- The first whole comparison retains both actual replacement arrows. -/
def firstMap : raw F q r ⟶ common F q p r s :=
  map F (firstQMap q p) (firstRMap r s)

/-- The second whole comparison retains both other actual replacement arrows. -/
def secondMap : raw F p s ⟶ common F q p r s :=
  map F (secondQMap q p) (secondRMap r s)

omit [ModelCategory S] [ModelCategory T] in
/-- Every comparison component is the original bifunctor on the two original maps. -/
theorem map_app {Q Q' : S ⥤ S} {R R' : T ⥤ T} (a : Q' ⟶ Q) (b : R ⟶ R') (N : S) (X : T) :
    (map F a b).app (op N, X) = F.map ((a.app N).op, b.app X) := rfl

omit [ModelCategory T] in
/-- The first source component is the original mapped counit. -/
theorem firstQMap_app (N : S) : (firstQMap q p).app N = q.Q.map (p.q.app N) := by
  simp [firstQMap]

omit [ModelCategory T] in
/-- The second source component is the original outer counit. -/
theorem secondQMap_app (N : S) : (secondQMap q p).app N = q.q.app (p.Q.obj N) := by
  simp [secondQMap]

omit [ModelCategory S] in
/-- The first target component is the original mapped unit. -/
theorem firstRMap_app (X : T) : (firstRMap r s).app X = r.R.map (s.r.app X) := by
  simp [firstRMap]

omit [ModelCategory S] in
/-- The second target component is the original outer unit. -/
theorem secondRMap_app (X : T) : (secondRMap r s).app X = r.r.app (s.R.obj X) := by
  simp [secondRMap]

/-- The first comparison is invertible by homotopicality on its actual endpoints. -/
theorem firstMap_isIso (hF : OnCofibrantFibrant F) : IsIso (firstMap F q p r s) := by
  let : ∀ Z, IsIso ((firstMap F q p r s).app Z) := fun Z => by
    rcases Z with ⟨N, X⟩
    change IsIso ((map F (firstQMap q p) (firstRMap r s)).app (op N.unop, X))
    rw [map_app, firstQMap_app, firstRMap_app]
    exact hF _ _ (q.q_cofibrant N.unop) (q.q_cofibrant (p.Q.obj N.unop))
      (r.r_fibrant X) (r.r_fibrant (s.R.obj X))
      (q.q_map_weak _ (p.q_trivialFibration N.unop).2)
      (r.r_map_weak _ (s.r_trivialCofibration X).2)
  exact NatIso.isIso_of_isIso_app _

/-- The second comparison is invertible by the same original endpoint calculation. -/
theorem secondMap_isIso (hF : OnCofibrantFibrant F) : IsIso (secondMap F q p r s) := by
  let : ∀ Z, IsIso ((secondMap F q p r s).app Z) := fun Z => by
    rcases Z with ⟨N, X⟩
    change IsIso ((map F (secondQMap q p) (secondRMap r s)).app (op N.unop, X))
    rw [map_app, secondQMap_app, secondRMap_app]
    exact hF _ _ (p.q_cofibrant N.unop) (q.q_cofibrant (p.Q.obj N.unop))
      (s.r_fibrant X) (r.r_fibrant (s.R.obj X))
      (q.q_trivialFibration (p.Q.obj N.unop)).2
      (r.r_trivialCofibration (s.R.obj X)).2
  exact NatIso.isIso_of_isIso_app _

/-- The first full bifunctor is isomorphic to the actual common bifunctor. -/
def firstIso (hF : OnCofibrantFibrant F) : raw F q r ≅ common F q p r s := by
  let : IsIso (firstMap F q p r s) := firstMap_isIso F q p r s hF
  exact asIso (firstMap F q p r s)

/-- The other full bifunctor is isomorphic to the same actual common bifunctor. -/
def secondIso (hF : OnCofibrantFibrant F) : raw F p s ≅ common F q p r s := by
  let : IsIso (secondMap F q p r s) := secondMap_isIso F q p r s hF
  exact asIso (secondMap F q p r s)

/-- Both caller Q/R choices give canonically isomorphic whole bifunctors. -/
def choiceIso (hF : OnCofibrantFibrant F) : raw F q r ≅ raw F p s :=
  firstIso F q p r s hF ≪≫ (secondIso F q p r s hF).symm

omit [ModelCategory T] in
/-- The source comparisons retain the entire original counit square. -/
theorem qCounitSquare : firstQMap q p ≫ q.q = secondQMap q p ≫ p.q := by
  apply NatTrans.ext
  funext N
  simp only [NatTrans.comp_app, firstQMap_app, secondQMap_app]
  exact q.q.naturality (p.q.app N)

omit [ModelCategory S] in
/-- The target comparisons retain the entire original unit square. -/
theorem rUnitSquare : r.r ≫ firstRMap r s = s.r ≫ secondRMap r s := by
  apply NatTrans.ext
  funext X
  simp only [NatTrans.comp_app, firstRMap_app, secondRMap_app]
  exact (r.r.naturality (s.r.app X)).symm

omit [ModelCategory S] [ModelCategory T] in
/-- Whole comparison maps compose using the actual source and target transformations. -/
theorem map_comp {Q₁ Q₂ Q₃ : S ⥤ S} {R₁ R₂ R₃ : T ⥤ T}
    (a : Q₂ ⟶ Q₁) (a' : Q₃ ⟶ Q₂) (b : R₁ ⟶ R₂) (b' : R₂ ⟶ R₃) :
    map F a b ≫ map F a' b' = map F (a' ≫ a) (b ≫ b') := by
  have h : NatTrans.prod (NatTrans.op a) b ≫ NatTrans.prod (NatTrans.op a') b' =
      NatTrans.prod (NatTrans.op (a' ≫ a)) (b ≫ b') := by
    apply NatTrans.ext
    funext Z
    rcases Z with ⟨N, X⟩
    rfl
  unfold map
  rw [← whiskerRight_comp, h]

/-- Both common legs commute with the same ordinary replacement comparison. -/
theorem ordinarySquare :
    ordinaryMap F q r ≫ firstMap F q p r s = ordinaryMap F p s ≫ secondMap F q p r s := by
  change map F q.q r.r ≫ map F (firstQMap q p) (firstRMap r s) =
    map F p.q s.r ≫ map F (secondQMap q p) (secondRMap r s)
  rw [map_comp, map_comp, qCounitSquare, rUnitSquare]

/-- Choice comparison preserves the ordinary bifunctor's original Q/R map. -/
theorem choiceIso_ordinary (hF : OnCofibrantFibrant F) :
    ordinaryMap F q r ≫ (choiceIso F q p r s hF).hom = ordinaryMap F p s := by
  change ordinaryMap F q r ≫ ((firstIso F q p r s hF).hom ≫ (secondIso F q p r s hF).inv) = _
  have h := congrArg
    (fun f : F ⟶ common F q p r s => f ≫ (secondIso F q p r s hF).inv)
    (ordinarySquare F q p r s)
  change (ordinaryMap F q r ≫ (firstIso F q p r s hF).hom) ≫ (secondIso F q p r s hF).inv =
    (ordinaryMap F p s ≫ (secondIso F q p r s hF).hom) ≫ (secondIso F q p r s hF).inv at h
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- Ordinary computation is invertible at every cofibrant/fibrant pair. -/
theorem ordinaryMap_app_isIso (hF : OnCofibrantFibrant F) (N : S) (X : T)
    (hN : IsCofibrant N) (hX : IsFibrant X) : IsIso ((ordinaryMap F q r).app (op N, X)) :=
  hF _ _ hN (q.q_cofibrant N) hX (r.r_fibrant X)
    (q.q_trivialFibration N).2 (r.r_trivialCofibration X).2

/-- The whole replaced bifunctor inverts both original weak-map variables. -/
theorem raw_inverts (hF : OnCofibrantFibrant F) :
    ((weakEquivalences S).op.prod (weakEquivalences T)).IsInvertedBy (raw F q r) := by
  rintro ⟨N, X⟩ ⟨N', X'⟩ ⟨f, g⟩ ⟨hf, hg⟩
  exact hF (q.Q.map f.unop) (r.R.map g) (q.q_cofibrant N.unop) (q.q_cofibrant N'.unop)
    (r.r_fibrant X) (r.r_fibrant X') (q.q_map_weak _ hf) (r.r_map_weak _ hg)

include q r in
/-- Cofibrant/fibrant components determine transformations into a weak-inverting target. -/
theorem natTrans_ext_of_cofibrant_fibrant {F₀ G : Sᵒᵖ × T ⥤ E}
    (hG : ((weakEquivalences S).op.prod (weakEquivalences T)).IsInvertedBy G) (a b : F₀ ⟶ G)
    (h : ∀ (N : S) (X : T), IsCofibrant N → IsFibrant X → a.app (op N, X) = b.app (op N, X)) :
    a = b := by
  apply NatTrans.ext
  funext Z
  rcases Z with ⟨N, X⟩
  let f : (N, X) ⟶ (op (q.Q.obj N.unop), r.R.obj X) := ((q.q.app N.unop).op, r.r.app X)
  let : IsIso (G.map f) := hG f ⟨(q.q_trivialFibration N.unop).2, (r.r_trivialCofibration X).2⟩
  apply (cancel_mono (G.map f)).mp
  rw [← a.naturality f, ← b.naturality f, h _ _ (q.q_cofibrant N.unop) (r.r_fibrant X)]

/-- The whole choice transformation is characterized by its ordinary comparison square. -/
theorem choiceIso_hom_unique (hF : OnCofibrantFibrant F) (a : raw F q r ⟶ raw F p s)
    (ha : ordinaryMap F q r ≫ a = ordinaryMap F p s) : a = (choiceIso F q p r s hF).hom := by
  apply natTrans_ext_of_cofibrant_fibrant q r (raw_inverts F p s hF)
  intro N X hN hX
  let : IsIso ((ordinaryMap F q r).app (op N, X)) := ordinaryMap_app_isIso F q r hF N X hN hX
  apply (cancel_epi ((ordinaryMap F q r).app (op N, X))).mp
  have h₁ := congr_app ha (op N, X)
  have h₂ := congr_app (choiceIso_ordinary F q p r s hF) (op N, X)
  exact h₁.trans h₂.symm

/-- Identical caller records give the identity on the entire bifunctor. -/
theorem choiceIso_refl (hF : OnCofibrantFibrant F) : choiceIso F q q r r hF = Iso.refl (raw F q r) := by
  apply Iso.ext
  exact (choiceIso_hom_unique F q q r r hF (𝟙 _) (Category.comp_id _)).symm

/-- Three caller records compose coherently on the entire bifunctor. -/
theorem choiceIso_trans (z : GeneratedFunctorialReplacements.Data (C := S))
    (t : GeneratedFunctorialReplacements.Data (C := T)) (hF : OnCofibrantFibrant F) :
    choiceIso F q p r s hF ≪≫ choiceIso F p z s t hF = choiceIso F q z r t hF := by
  apply Iso.ext
  apply choiceIso_hom_unique F q z r t hF
  simp only [Iso.trans_hom]
  rw [← Category.assoc, choiceIso_ordinary, choiceIso_ordinary]

end HomotopicalAlgebra.CofibrantFibrantBifunctorChoices
