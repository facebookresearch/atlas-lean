/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Products.Additive
public import MathlibExt.CategoryTheory.ExactCategory.Basic
public import MathlibExt.CategoryTheory.ExactCategory.Split

/-!
# Exact structure on product categories

For exact categories `C` and `D`, the product `C × D` carries a componentwise
exact structure: a short complex `S` in `C × D` is admissible exact iff its
images under the additive projections `Prod.fst` and `Prod.snd` are admissible
exact in `C` and `D`.

Nonclaims: no biproduct-functor exactness, no Waldhausen additivity, no K/G-theory,
no realization, no spectra, no Q/S comparison, no n-ary products, no abelian or
monoidal claims.
-/

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C]
  [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D]
  [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D]

/-- Admissible exactness in a product is componentwise. -/
def prodIsAdmissibleExact (S : ShortComplex (C × D)) : Prop :=
  ExactCategory.IsAdmissibleExact (S.map (Prod.fst C D)) ∧
    ExactCategory.IsAdmissibleExact (S.map (Prod.snd C D))

/-- Admissible exactness in `C × D` holds iff it holds after both projections. -/
@[simp]
theorem prod_isAdmissibleExact_iff (S : ShortComplex (C × D)) :
    prodIsAdmissibleExact C D S ↔
      ExactCategory.IsAdmissibleExact (S.map (Prod.fst C D)) ∧
        ExactCategory.IsAdmissibleExact (S.map (Prod.snd C D)) :=
  Iff.rfl

namespace ProdExact

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- A morphism in a product is mono when both components are mono. -/
lemma mono_of_components {X Y : C × D} (f : X ⟶ Y)
    [Mono f.1] [Mono f.2] : Mono f where
  right_cancellation := by
    intro W g h eq
    have h1 : g.1 ≫ f.1 = h.1 ≫ f.1 := congrArg (fun k => k.1) eq
    have h2 : g.2 ≫ f.2 = h.2 ≫ f.2 := congrArg (fun k => k.2) eq
    have e1 : g.1 = h.1 := (cancel_mono f.1).mp h1
    have e2 : g.2 = h.2 := (cancel_mono f.2).mp h2
    apply Prod.hom_ext <;> assumption

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- A morphism in a product is epi when both components are epi. -/
lemma epi_of_components {X Y : C × D} (f : X ⟶ Y)
    [Epi f.1] [Epi f.2] : Epi f where
  left_cancellation := by
    intro W g h eq
    have h1 : f.1 ≫ g.1 = f.1 ≫ h.1 := congrArg (fun k => k.1) eq
    have h2 : f.2 ≫ g.2 = f.2 ≫ h.2 := congrArg (fun k => k.2) eq
    have e1 : g.1 = h.1 := (cancel_epi f.1).mp h1
    have e2 : g.2 = h.2 := (cancel_epi f.2).mp h2
    apply Prod.hom_ext <;> assumption

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- A pair of zero objects is zero in the product. -/
lemma isZero_of_components {H1 : C} {H2 : D}
    (h1 : IsZero H1) (h2 : IsZero H2) : IsZero (H1, H2) :=
  isZero_prod_iff C D |>.mpr ⟨h1, h2⟩

/-- Kernel limits in a product combine componentwise. -/
noncomputable def kernelIsLimitOfComponents (S : ShortComplex (C × D))
    (hC : IsLimit (KernelFork.ofι (S.map (Prod.fst C D)).f (S.map (Prod.fst C D)).zero))
    (hD : IsLimit (KernelFork.ofι (S.map (Prod.snd C D)).f (S.map (Prod.snd C D)).zero)) :
    IsLimit (KernelFork.ofι S.f S.zero) := by
  refine Fork.IsLimit.mk _ (fun s => ((hC.lift (KernelFork.ofι ((_root_.Prod.fst s.ι)) (by
      have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
      have h := congrArg _root_.Prod.fst h0
      exact h))) ,
    (hD.lift (KernelFork.ofι ((_root_.Prod.snd s.ι)) (by
      have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
      have h := congrArg _root_.Prod.snd h0
      exact h))))) ?_ ?_
  · intro s
    refine Prod.hom_ext (Fork.IsLimit.lift_ι hC) (Fork.IsLimit.lift_ι hD)
  · intro s m hm
    refine Prod.hom_ext ?_ ?_
    · apply Fork.IsLimit.hom_ext hC
      have hCw : (_root_.Prod.fst s.ι) ≫ (S.map (Prod.fst C D)).g = 0 := by
        have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
        have h := congrArg _root_.Prod.fst h0
        exact h
      have h1 : _root_.Prod.fst m ≫ (S.map (Prod.fst C D)).f =
        _root_.Prod.fst s.ι := by
        have := congrArg _root_.Prod.fst hm
        exact this
      have h2 : (hC.lift (KernelFork.ofι (_root_.Prod.fst s.ι) hCw)) ≫
        (S.map (Prod.fst C D)).f = _root_.Prod.fst s.ι :=
        Fork.IsLimit.lift_ι hC
      exact h1.trans h2.symm
    · apply Fork.IsLimit.hom_ext hD
      have hDw : (_root_.Prod.snd s.ι) ≫ (S.map (Prod.snd C D)).g = 0 := by
        have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
        have h := congrArg _root_.Prod.snd h0
        exact h
      have h1 : _root_.Prod.snd m ≫ (S.map (Prod.snd C D)).f =
        _root_.Prod.snd s.ι := by
        have := congrArg _root_.Prod.snd hm
        exact this
      have h2 : (hD.lift (KernelFork.ofι (_root_.Prod.snd s.ι) hDw)) ≫
        (S.map (Prod.snd C D)).f = _root_.Prod.snd s.ι :=
        Fork.IsLimit.lift_ι hD
      exact h1.trans h2.symm

/-- Cokernel colimits in a product combine componentwise. -/
noncomputable def cokernelIsColimitOfComponents (S : ShortComplex (C × D))
    (hC : IsColimit (CokernelCofork.ofπ (S.map (Prod.fst C D)).g (S.map (Prod.fst C D)).zero))
    (hD : IsColimit (CokernelCofork.ofπ (S.map (Prod.snd C D)).g (S.map (Prod.snd C D)).zero)) :
    IsColimit (CokernelCofork.ofπ S.g S.zero) := by
  refine Cofork.IsColimit.mk _ (fun s => ((hC.desc (CokernelCofork.ofπ (_root_.Prod.fst s.π) (by
      have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
      have h := congrArg _root_.Prod.fst h0
      exact h))) ,
    (hD.desc (CokernelCofork.ofπ (_root_.Prod.snd s.π) (by
      have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
      have h := congrArg _root_.Prod.snd h0
      exact h))))) ?_ ?_
  · intro s
    refine Prod.hom_ext (Cofork.IsColimit.π_desc hC) (Cofork.IsColimit.π_desc hD)
  · intro s m hm
    refine Prod.hom_ext ?_ ?_
    · apply Cofork.IsColimit.hom_ext hC
      have hCw : (S.map (Prod.fst C D)).f ≫ (_root_.Prod.fst s.π) = 0 := by
        have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
        have h := congrArg _root_.Prod.fst h0
        exact h
      have h1 : (S.map (Prod.fst C D)).g ≫ _root_.Prod.fst m =
        _root_.Prod.fst s.π := by
        have := congrArg _root_.Prod.fst hm
        exact this
      have h2 : (S.map (Prod.fst C D)).g ≫
        (hC.desc (CokernelCofork.ofπ (_root_.Prod.fst s.π) hCw)) =
        _root_.Prod.fst s.π :=
        Cofork.IsColimit.π_desc hC
      exact h1.trans h2.symm
    · apply Cofork.IsColimit.hom_ext hD
      have hDw : (S.map (Prod.snd C D)).f ≫ (_root_.Prod.snd s.π) = 0 := by
        have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
        have h := congrArg _root_.Prod.snd h0
        exact h
      have h1 : (S.map (Prod.snd C D)).g ≫ _root_.Prod.snd m =
        _root_.Prod.snd s.π := by
        have := congrArg _root_.Prod.snd hm
        exact this
      have h2 : (S.map (Prod.snd C D)).g ≫
        (hD.desc (CokernelCofork.ofπ (_root_.Prod.snd s.π) hDw)) =
        _root_.Prod.snd s.π :=
        Cofork.IsColimit.π_desc hD
      exact h1.trans h2.symm

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- Pushouts in a product combine componentwise. -/
theorem pushoutIsColimit_of_components
    {Z X Y : C × D} (f : Z ⟶ X) (g : Z ⟶ Y)
    {P1 : C} {inl1 : X.1 ⟶ P1} {inr1 : Y.1 ⟶ P1}
    (hC : IsPushout f.1 g.1 inl1 inr1)
    {P2 : D} {inl2 : X.2 ⟶ P2} {inr2 : Y.2 ⟶ P2}
    (hD : IsPushout f.2 g.2 inl2 inr2) :
    IsPushout f g (Prod.mkHom inl1 inl2) (Prod.mkHom inr1 inr2) :=
  isPushout_prod_iff C D |>.mpr ⟨hC, hD⟩

omit [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [Preadditive D] [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- Pullbacks in a product combine componentwise. -/
theorem pullbackIsLimit_of_components
    {X Y Z : C × D} (f : X ⟶ Z) (g : Y ⟶ Z)
    {P1 : C} {fst1 : P1 ⟶ X.1} {snd1 : P1 ⟶ Y.1}
    (hC : IsPullback fst1 snd1 f.1 g.1)
    {P2 : D} {fst2 : P2 ⟶ X.2} {snd2 : P2 ⟶ Y.2}
    (hD : IsPullback fst2 snd2 f.2 g.2) :
    IsPullback (Prod.mkHom fst1 fst2) (Prod.mkHom snd1 snd2) f g :=
  isPullback_prod_iff C D |>.mpr ⟨hC, hD⟩

/-- Left homology data in a product combines componentwise. -/
noncomputable def leftHomologyDataOfComponents (S : ShortComplex (C × D))
    (hC : (S.map (Prod.fst C D)).LeftHomologyData)
    (hD : (S.map (Prod.snd C D)).LeftHomologyData) :
    S.LeftHomologyData := by
  let K : C × D := (hC.K, hD.K)
  let H : C × D := (hC.H, hD.H)
  let ii : K ⟶ S.X₂ := Prod.mkHom hC.i hD.i
  let pp : K ⟶ H := Prod.mkHom hC.π hD.π
  have wi : ii ≫ S.g = 0 := by
    apply Prod.hom_ext
    · exact hC.wi
    · exact hD.wi
  let hi : IsLimit (KernelFork.ofι ii wi) := by
    refine Fork.IsLimit.mk _ (fun (s : KernelFork S.g) =>
      Prod.mkHom
        (hC.hi.lift (KernelFork.ofι (_root_.Prod.fst s.ι) (by
          have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h)))
        (hD.hi.lift (KernelFork.ofι (_root_.Prod.snd s.ι) (by
          have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h)))) ?_ ?_
    · intro s
      refine Prod.hom_ext (Fork.IsLimit.lift_ι hC.hi) (Fork.IsLimit.lift_ι hD.hi)
    · intro s m hm
      refine Prod.hom_ext ?_ ?_
      · apply Fork.IsLimit.hom_ext hC.hi
        have hw : (_root_.Prod.fst s.ι) ≫ (S.map (Prod.fst C D)).g = 0 := by
          have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h
        have h1 : (_root_.Prod.fst m) ≫ hC.i = (_root_.Prod.fst s.ι) := by
          have h := congrArg (fun k => k.1) hm
          exact h
        have h2 : (hC.hi.lift (KernelFork.ofι (_root_.Prod.fst s.ι) hw)) ≫ hC.i =
          (_root_.Prod.fst s.ι) := Fork.IsLimit.lift_ι hC.hi
        exact h1.trans h2.symm
      · apply Fork.IsLimit.hom_ext hD.hi
        have hw : (_root_.Prod.snd s.ι) ≫ (S.map (Prod.snd C D)).g = 0 := by
          have h0 : s.ι ≫ S.g = 0 := KernelFork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h
        have h1 : (_root_.Prod.snd m) ≫ hD.i = (_root_.Prod.snd s.ι) := by
          have h := congrArg (fun k => k.2) hm
          exact h
        have h2 : (hD.hi.lift (KernelFork.ofι (_root_.Prod.snd s.ι) hw)) ≫ hD.i =
          (_root_.Prod.snd s.ι) := Fork.IsLimit.lift_ι hD.hi
        exact h1.trans h2.symm
  have wπ : hi.lift (KernelFork.ofι S.f S.zero) ≫ pp = 0 := by
    apply Prod.hom_ext
    · exact hC.wπ
    · exact hD.wπ
  let ff : S.X₁ ⟶ K := hi.lift (KernelFork.ofι S.f S.zero)
  have hπ : IsColimit (CokernelCofork.ofπ pp wπ) := by
    refine Cofork.IsColimit.mk _ (fun (s : CokernelCofork ff) =>
      Prod.mkHom
        (hC.hπ.desc (CokernelCofork.ofπ (_root_.Prod.fst s.π) (by
          have h0 : ff ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h)))
        (hD.hπ.desc (CokernelCofork.ofπ (_root_.Prod.snd s.π) (by
          have h0 : ff ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h)))) ?_ ?_
    · intro s
      refine Prod.hom_ext (Cofork.IsColimit.π_desc hC.hπ) (Cofork.IsColimit.π_desc hD.hπ)
    · intro s m hm
      refine Prod.hom_ext ?_ ?_
      · apply Cofork.IsColimit.hom_ext hC.hπ
        have hw : ff.1 ≫ (_root_.Prod.fst s.π) = 0 := by
          have h0 : ff ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h
        have h1 : hC.π ≫ (_root_.Prod.fst m) = (_root_.Prod.fst s.π) := by
          have h := congrArg (fun k => k.1) hm
          exact h
        have h2 : hC.π ≫ (hC.hπ.desc (CokernelCofork.ofπ (_root_.Prod.fst s.π) hw)) =
          (_root_.Prod.fst s.π) := Cofork.IsColimit.π_desc hC.hπ
        exact h1.trans h2.symm
      · apply Cofork.IsColimit.hom_ext hD.hπ
        have hw : ff.2 ≫ (_root_.Prod.snd s.π) = 0 := by
          have h0 : ff ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h
        have h1 : hD.π ≫ (_root_.Prod.snd m) = (_root_.Prod.snd s.π) := by
          have h := congrArg (fun k => k.2) hm
          exact h
        have h2 : hD.π ≫ (hD.hπ.desc (CokernelCofork.ofπ (_root_.Prod.snd s.π) hw)) =
          (_root_.Prod.snd s.π) := Cofork.IsColimit.π_desc hD.hπ
        exact h1.trans h2.symm
  exact { K := K, H := H, i := ii, π := pp, wi := wi, hi := hi, wπ := wπ, hπ := hπ }

/-- Right homology data in a product combines componentwise. -/
noncomputable def rightHomologyDataOfComponents (S : ShortComplex (C × D))
    (hC : (S.map (Prod.fst C D)).RightHomologyData)
    (hD : (S.map (Prod.snd C D)).RightHomologyData) :
    S.RightHomologyData := by
  let Q : C × D := (hC.Q, hD.Q)
  let H : C × D := (hC.H, hD.H)
  let pp : S.X₂ ⟶ Q := Prod.mkHom hC.p hD.p
  let ii : H ⟶ Q := Prod.mkHom hC.ι hD.ι
  have wp : S.f ≫ pp = 0 := by
    apply Prod.hom_ext
    · exact hC.wp
    · exact hD.wp
  let hp : IsColimit (CokernelCofork.ofπ pp wp) := by
    refine Cofork.IsColimit.mk _ (fun (s : CokernelCofork S.f) =>
      Prod.mkHom
        (hC.hp.desc (CokernelCofork.ofπ (_root_.Prod.fst s.π) (by
          have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h)))
        (hD.hp.desc (CokernelCofork.ofπ (_root_.Prod.snd s.π) (by
          have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h)))) ?_ ?_
    · intro s
      refine Prod.hom_ext (Cofork.IsColimit.π_desc hC.hp) (Cofork.IsColimit.π_desc hD.hp)
    · intro s m hm
      refine Prod.hom_ext ?_ ?_
      · apply Cofork.IsColimit.hom_ext hC.hp
        have hw : S.f.1 ≫ (_root_.Prod.fst s.π) = 0 := by
          have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h
        have h1 : pp.1 ≫ (_root_.Prod.fst m) = (_root_.Prod.fst s.π) := by
          have h := congrArg (fun k => k.1) hm
          exact h
        have h2 : pp.1 ≫ (hC.hp.desc (CokernelCofork.ofπ (_root_.Prod.fst s.π) hw)) =
          (_root_.Prod.fst s.π) := Cofork.IsColimit.π_desc hC.hp
        exact h1.trans h2.symm
      · apply Cofork.IsColimit.hom_ext hD.hp
        have hw : S.f.2 ≫ (_root_.Prod.snd s.π) = 0 := by
          have h0 : S.f ≫ s.π = 0 := CokernelCofork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h
        have h1 : pp.2 ≫ (_root_.Prod.snd m) = (_root_.Prod.snd s.π) := by
          have h := congrArg (fun k => k.2) hm
          exact h
        have h2 : pp.2 ≫ (hD.hp.desc (CokernelCofork.ofπ (_root_.Prod.snd s.π) hw)) =
          (_root_.Prod.snd s.π) := Cofork.IsColimit.π_desc hD.hp
        exact h1.trans h2.symm
  have wι : ii ≫ hp.desc (CokernelCofork.ofπ S.g S.zero) = 0 := by
    apply Prod.hom_ext
    · exact hC.wι
    · exact hD.wι
  have hι : IsLimit (KernelFork.ofι ii wι) := by
    refine Fork.IsLimit.mk _
      (fun (s : KernelFork (hp.desc (CokernelCofork.ofπ S.g S.zero))) =>
        Prod.mkHom
          (hC.hι.lift (KernelFork.ofι (_root_.Prod.fst s.ι) (by
            have h0 : s.ι ≫ hp.desc (CokernelCofork.ofπ S.g S.zero) = 0 :=
              KernelFork.condition s
            have h := congrArg (fun k => k.1) h0
            exact h)))
          (hD.hι.lift (KernelFork.ofι (_root_.Prod.snd s.ι) (by
            have h0 : s.ι ≫ hp.desc (CokernelCofork.ofπ S.g S.zero) = 0 :=
              KernelFork.condition s
            have h := congrArg (fun k => k.2) h0
            exact h)))) ?_ ?_
    · intro s
      refine Prod.hom_ext (Fork.IsLimit.lift_ι hC.hι) (Fork.IsLimit.lift_ι hD.hι)
    · intro s m hm
      refine Prod.hom_ext ?_ ?_
      · apply Fork.IsLimit.hom_ext hC.hι
        have h1 : (_root_.Prod.fst m) ≫ hC.ι = (_root_.Prod.fst s.ι) := by
          have h := congrArg (fun k => k.1) hm
          exact h
        have h2 : (hC.hι.lift (KernelFork.ofι (_root_.Prod.fst s.ι) (by
          have h0 := KernelFork.condition s
          have h := congrArg (fun k => k.1) h0
          exact h))) ≫ hC.ι =
          (_root_.Prod.fst s.ι) := Fork.IsLimit.lift_ι hC.hι
        exact h1.trans h2.symm
      · apply Fork.IsLimit.hom_ext hD.hι
        have h1 : (_root_.Prod.snd m) ≫ hD.ι = (_root_.Prod.snd s.ι) := by
          have h := congrArg (fun k => k.2) hm
          exact h
        have h2 : (hD.hι.lift (KernelFork.ofι (_root_.Prod.snd s.ι) (by
          have h0 := KernelFork.condition s
          have h := congrArg (fun k => k.2) h0
          exact h))) ≫ hD.ι =
          (_root_.Prod.snd s.ι) := Fork.IsLimit.lift_ι hD.hι
        exact h1.trans h2.symm
  exact { Q := Q, H := H, p := pp, ι := ii, wp := wp, hp := hp, wι := wι, hι := hι }

/-- Homology data in a product combines componentwise. -/
noncomputable def homologyDataOfComponents (S : ShortComplex (C × D))
    (hC : (S.map (Prod.fst C D)).HomologyData)
    (hD : (S.map (Prod.snd C D)).HomologyData) :
    S.HomologyData where
  left := leftHomologyDataOfComponents C D S hC.left hD.left
  right := rightHomologyDataOfComponents C D S hC.right hD.right
  iso :=
    { hom := Prod.mkHom hC.iso.hom hD.iso.hom
      inv := Prod.mkHom hC.iso.inv hD.iso.inv
      hom_inv_id := by
        apply Prod.hom_ext
        · exact hC.iso.hom_inv_id
        · exact hD.iso.hom_inv_id
      inv_hom_id := by
        apply Prod.hom_ext
        · exact hC.iso.inv_hom_id
        · exact hD.iso.inv_hom_id }
  comm := by
    apply Prod.hom_ext
    · exact hC.comm
    · exact hD.comm

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- Exactness in a product follows from componentwise exactness. -/
theorem exact_of_components (S : ShortComplex (C × D))
    (hC : (S.map (Prod.fst C D)).Exact)
    (hD : (S.map (Prod.snd C D)).Exact) :
    S.Exact := by
  obtain ⟨hCdata, hC0⟩ := hC.condition
  obtain ⟨hDdata, hD0⟩ := hD.condition
  exact ⟨homologyDataOfComponents C D S hCdata hDdata,
    isZero_of_components C D hC0 hD0⟩

omit [HasZeroObject C] [HasBinaryBiproducts C] [ExactCategory C]
    [HasZeroObject D] [HasBinaryBiproducts D] [ExactCategory D] in
/-- Short exactness in a product follows from componentwise short exactness. -/
theorem shortExact_of_components (S : ShortComplex (C × D))
    (hC : (S.map (Prod.fst C D)).ShortExact)
    (hD : (S.map (Prod.snd C D)).ShortExact) :
    S.ShortExact := by
  have : Mono S.f.1 := hC.mono_f
  have : Mono S.f.2 := hD.mono_f
  have : Epi S.g.1 := hC.epi_g
  have : Epi S.g.2 := hD.epi_g
  have := mono_of_components C D S.f
  have := epi_of_components C D S.g
  exact ShortComplex.ShortExact.mk' (exact_of_components C D S hC.exact hD.exact)
    inferInstance inferInstance

/-- Componentwise exact structure on a product of exact categories. -/
noncomputable instance prodExactCategory : ExactCategory (C × D) where
  IsAdmissibleExact := prodIsAdmissibleExact C D
  shortExact_of_isAdmissibleExact := fun {S} h =>
    shortExact_of_components C D S
      (ExactCategory.shortExact_of_isAdmissibleExact h.1)
      (ExactCategory.shortExact_of_isAdmissibleExact h.2)
  isLimit_kernelFork := fun {S} h =>
    ⟨kernelIsLimitOfComponents C D S
      (ExactCategory.isLimit_kernelFork h.1).some
      (ExactCategory.isLimit_kernelFork h.2).some⟩
  isColimit_cokernelCofork := fun {S} h =>
    ⟨cokernelIsColimitOfComponents C D S
      (ExactCategory.isColimit_cokernelCofork h.1).some
      (ExactCategory.isColimit_cokernelCofork h.2).some⟩
  isAdmissibleExact_of_iso := fun {S T} e h =>
    ⟨ExactCategory.isAdmissibleExact_of_iso
        ((Prod.fst C D).mapShortComplex.mapIso e) h.1,
      ExactCategory.isAdmissibleExact_of_iso
        ((Prod.snd C D).mapShortComplex.mapIso e) h.2⟩
  isAdmissibleExact_split := fun X Y =>
    ⟨ExactCategory.isAdmissibleExact_of_splitting
        ((ShortComplex.Splitting.ofHasBinaryBiproduct X Y).map (Prod.fst C D)),
      ExactCategory.isAdmissibleExact_of_splitting
        ((ShortComplex.Splitting.ofHasBinaryBiproduct X Y).map (Prod.snd C D))⟩
  admissibleMono_comp := by
    constructor
    intro X Y Z f g hf hg
    obtain ⟨Zf, pf, wf, hfS⟩ := hf
    obtain ⟨Zg, pg, wg, hgS⟩ := hg
    have hf1 : admissibleMonosOf C _ f.1 := ⟨_, _, _, hfS.1⟩
    have hg1 : admissibleMonosOf C _ g.1 := ⟨_, _, _, hgS.1⟩
    have hf2 : admissibleMonosOf D _ f.2 := ⟨_, _, _, hfS.2⟩
    have hg2 : admissibleMonosOf D _ g.2 := ⟨_, _, _, hgS.2⟩
    have hcomp1 := ExactCategory.admissibleMono_comp.comp_mem f.1 g.1 hf1 hg1
    have hcomp2 := ExactCategory.admissibleMono_comp.comp_mem f.2 g.2 hf2 hg2
    obtain ⟨ZC1, pC1, wC1, hC1⟩ := hcomp1
    obtain ⟨ZC2, pC2, wC2, hC2⟩ := hcomp2
    refine ⟨(ZC1, ZC2), Prod.mkHom pC1 pC2, ?_, ⟨?_, ?_⟩⟩
    · apply Prod.hom_ext
      · exact wC1
      · exact wC2
    · exact hC1
    · exact hC2
  admissibleEpi_comp := by
    constructor
    intro X Y Z f g hf hg
    obtain ⟨Xf, ff, wf, hfS⟩ := hf
    obtain ⟨Xg, fg, wg, hgS⟩ := hg
    have hf1 : admissibleEpisOf C _ f.1 := ⟨_, _, _, hfS.1⟩
    have hg1 : admissibleEpisOf C _ g.1 := ⟨_, _, _, hgS.1⟩
    have hf2 : admissibleEpisOf D _ f.2 := ⟨_, _, _, hfS.2⟩
    have hg2 : admissibleEpisOf D _ g.2 := ⟨_, _, _, hgS.2⟩
    have hcomp1 := ExactCategory.admissibleEpi_comp.comp_mem f.1 g.1 hf1 hg1
    have hcomp2 := ExactCategory.admissibleEpi_comp.comp_mem f.2 g.2 hf2 hg2
    obtain ⟨XC1, fC1, wC1, hC1⟩ := hcomp1
    obtain ⟨XC2, fC2, wC2, hC2⟩ := hcomp2
    refine ⟨(XC1, XC2), Prod.mkHom fC1 fC2, ?_, ⟨?_, ?_⟩⟩
    · apply Prod.hom_ext
      · exact wC1
      · exact wC2
    · exact hC1
    · exact hC2
  admissibleMono_pushout := by
    intro X Y i hi X' f
    obtain ⟨Zf, pf, wf, hfS⟩ := hi
    have hi1 : admissibleMonosOf C _ i.1 := ⟨_, _, _, hfS.1⟩
    have hi2 : admissibleMonosOf D _ i.2 := ⟨_, _, _, hfS.2⟩
    obtain ⟨P1, inl1, inr1, hpush1, had1⟩ :=
      ExactCategory.admissibleMono_pushout X.1 Y.1 i.1 hi1 X'.1 f.1
    obtain ⟨P2, inl2, inr2, hpush2, had2⟩ :=
      ExactCategory.admissibleMono_pushout X.2 Y.2 i.2 hi2 X'.2 f.2
    obtain ⟨ZC1, pC1, wC1, hC1⟩ := had1
    obtain ⟨ZC2, pC2, wC2, hC2⟩ := had2
    refine ⟨(P1, P2), Prod.mkHom inl1 inl2, Prod.mkHom inr1 inr2,
      pushoutIsColimit_of_components C D f i hpush1 hpush2, ?_⟩
    refine ⟨(ZC1, ZC2), Prod.mkHom pC1 pC2, ?_, ⟨?_, ?_⟩⟩
    · apply Prod.hom_ext
      · exact wC1
      · exact wC2
    · exact hC1
    · exact hC2
  admissibleEpi_pullback := by
    intro Y Z p hp Z' g
    obtain ⟨Xf, ff, wf, hfS⟩ := hp
    have hp1 : admissibleEpisOf C _ p.1 := ⟨_, _, _, hfS.1⟩
    have hp2 : admissibleEpisOf D _ p.2 := ⟨_, _, _, hfS.2⟩
    obtain ⟨P1, fst1, snd1, hpull1, had1⟩ :=
      ExactCategory.admissibleEpi_pullback Y.1 Z.1 p.1 hp1 Z'.1 g.1
    obtain ⟨P2, fst2, snd2, hpull2, had2⟩ :=
      ExactCategory.admissibleEpi_pullback Y.2 Z.2 p.2 hp2 Z'.2 g.2
    obtain ⟨XC1, fC1, wC1, hC1⟩ := had1
    obtain ⟨XC2, fC2, wC2, hC2⟩ := had2
    refine ⟨(P1, P2), Prod.mkHom fst1 fst2, Prod.mkHom snd1 snd2,
      pullbackIsLimit_of_components C D g p hpull1 hpull2, ?_⟩
    refine ⟨(XC1, XC2), Prod.mkHom fC1 fC2, ?_, ⟨?_, ?_⟩⟩
    · apply Prod.hom_ext
      · exact wC1
      · exact wC2
    · exact hC1
    · exact hC2

/-! Legacy namespace aliases for the componentwise limit and homology helpers. -/
section LegacyHelperNames

open _root_.CategoryTheory.ProdExact renaming
  kernelIsLimitOfComponents → CategoryTheory.kernelIsLimit_of_components,
  cokernelIsColimitOfComponents → CategoryTheory.cokernelIsColimit_of_components,
  leftHomologyDataOfComponents → CategoryTheory.leftHomologyData_of_components,
  rightHomologyDataOfComponents → CategoryTheory.rightHomologyData_of_components,
  homologyDataOfComponents → CategoryTheory.homologyData_of_components

export _root_.CategoryTheory (kernelIsLimit_of_components cokernelIsColimit_of_components
  leftHomologyData_of_components rightHomologyData_of_components homologyData_of_components)

end LegacyHelperNames

end ProdExact

/-- Admissible monomorphisms for the componentwise product exact structure
are exactly the pairs of admissible monomorphisms in the factors. -/
theorem prod_isAdmissibleMono_iff {X Y : C × D} (f : X ⟶ Y) :
    ExactCategory.IsAdmissibleMono f ↔
      ExactCategory.IsAdmissibleMono f.1 ∧ ExactCategory.IsAdmissibleMono f.2 := by
  constructor
  · rintro ⟨Z, p, w, hC, hD⟩
    exact ⟨⟨Z.1, p.1, congrArg (fun k : X ⟶ Z => k.1) w, hC⟩,
      ⟨Z.2, p.2, congrArg (fun k : X ⟶ Z => k.2) w, hD⟩⟩
  · rintro ⟨⟨ZC, pC, wC, hC⟩, ⟨ZD, pD, wD, hD⟩⟩
    exact ⟨(ZC, ZD), Prod.mkHom pC pD, Prod.hom_ext wC wD, hC, hD⟩

/-- Admissible epimorphisms for the componentwise product exact structure
are exactly the pairs of admissible epimorphisms in the factors. -/
theorem prod_isAdmissibleEpi_iff {X Y : C × D} (f : X ⟶ Y) :
    ExactCategory.IsAdmissibleEpi f ↔
      ExactCategory.IsAdmissibleEpi f.1 ∧ ExactCategory.IsAdmissibleEpi f.2 := by
  constructor
  · rintro ⟨Z, i, w, hC, hD⟩
    exact ⟨⟨Z.1, i.1, congrArg (fun k : Z ⟶ Y => k.1) w, hC⟩,
      ⟨Z.2, i.2, congrArg (fun k : Z ⟶ Y => k.2) w, hD⟩⟩
  · rintro ⟨⟨ZC, iC, wC, hC⟩, ⟨ZD, iD, wD, hD⟩⟩
    exact ⟨(ZC, ZD), Prod.mkHom iC iD, Prod.hom_ext wC wD, hC, hD⟩

end CategoryTheory
