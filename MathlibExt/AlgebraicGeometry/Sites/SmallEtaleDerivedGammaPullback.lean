/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado

module

public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleGammaPullback
public import MathlibExt.CategoryTheory.Abelian.DeltaFunctor.PrecompositionCoherence
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleInverseImageExactness
public import MathlibExt.CategoryTheory.Abelian.RightDerived.DeltaFunctor

/-!
# Pullback of derived global sections

Let f : X → Y be a scheme morphism in universe u and c = max(u, w).
Global sections of AddCommGrpCat c-valued étale sheaves have right derived
functors RᑫΓ_X and RᑫΓ_Y. Exact inverse image f* lets the canonical
degree-zero pullback extend uniquely to a morphism of cohomological
delta functors.

Its degree q component is
RᑫΓ_Y(Q) → RᑫΓ_X(f*Q).
These maps commute with connecting homomorphisms, with identity maps after
the inverse-image identity comparison, and with composition after the
iterated/direct inverse-image comparison. All degrees q ∈ ℕ are included;
the coefficient universe w is independent of u.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections

/-- For a scheme X in universe u and c = max(u, w), this is the
cohomological delta functor (RᑫΓ_X)_(q∈ℕ) on abelian étale sheaves with
coefficients in c, equipped with the connecting maps of short exact sequences. -/
abbrev smallEtaleGammaDeltaFunctor (X : Scheme.{u}) :=
  Functor.rightDerivedDeltaFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w})

theorem smallEtaleGammaDeltaFunctor_universal (X : Scheme.{u}) :
    CohomologicalDeltaFunctor.IsUniversal
      (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}) AddCommGrpCat.{max u w}
      (smallEtaleGammaDeltaFunctor.{u, w} X) :=
  Functor.isUniversal_rightDerivedDeltaFunctor
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w})

local instance smallEtaleDerivedInverseImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleInverseImage.{u, w} f).Additive := smallEtaleInverseImage_additive.{u, w} f

theorem smallEtaleDerivedInputShortExact {X Y : Scheme.{u}} (f : X ⟶ Y)
    (S : ShortComplex (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max u w})) (hS : S.ShortExact) :
    (S.map (smallEtaleInverseImage.{u, w} f)).ShortExact :=
  smallEtaleInverseImage_shortExact.{u, w} f S hS

/-- For f : X → Y a scheme morphism in universe u and c = max(u, w),
the degree-zero global-section pullback extends to the morphism of
cohomological delta functors
(RᑫΓ_Y) → (Q ↦ RᑫΓ_X(f*Q)).
The target uses the short exact sequences preserved by f*. -/
def smallEtaleDerivedGammaPullbackDeltaHom {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleGammaDeltaFunctor.{u, w} Y ⟶
      CohomologicalDeltaFunctor.precompose (smallEtaleInverseImage.{u, w} f)
        (smallEtaleDerivedInputShortExact.{u, w} f) (smallEtaleGammaDeltaFunctor.{u, w} X) :=
  CohomologicalDeltaFunctor.normalizedExtension
    (smallEtaleGammaDeltaFunctor.{u, w} Y)
    (CohomologicalDeltaFunctor.precompose (smallEtaleInverseImage.{u, w} f)
      (smallEtaleDerivedInputShortExact.{u, w} f) (smallEtaleGammaDeltaFunctor.{u, w} X))
    (smallEtaleGammaDeltaFunctor_universal.{u, w} Y)
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
    (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} f)
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf)
    (smallEtalePullbackGlobalSections.{u, w} f)

/-- For f : X → Y a scheme morphism in universe u, c = max(u, w),
and q ∈ ℕ, this is the natural additive map
RᑫΓ_Y(Q) → RᑫΓ_X(f*Q) for abelian étale sheaves Q on Y.
It is the degree q part of the normalized delta-functor pullback. -/
def smallEtaleDerivedGammaPullback {X Y : Scheme.{u}} (f : X ⟶ Y) (q : ℕ) :
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q ⟶
      smallEtaleInverseImage.{u, w} f ⋙
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q :=
  CohomologicalDeltaFunctor.Hom.app (smallEtaleDerivedGammaPullbackDeltaHom.{u, w} f) q

theorem smallEtaleDerivedGammaPullback_zero {X Y : Scheme.{u}} (f : X ⟶ Y) :
    smallEtaleDerivedGammaPullback.{u, w} f 0 ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} f)
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom =
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom ≫
      smallEtalePullbackGlobalSections.{u, w} f :=
  CohomologicalDeltaFunctor.normalizedExtension_normalization
    (smallEtaleGammaDeltaFunctor.{u, w} Y)
    (CohomologicalDeltaFunctor.precompose (smallEtaleInverseImage.{u, w} f)
      (smallEtaleDerivedInputShortExact.{u, w} f) (smallEtaleGammaDeltaFunctor.{u, w} X))
    (smallEtaleGammaDeltaFunctor_universal.{u, w} Y)
    (Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf
    (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} f)
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf)
    (smallEtalePullbackGlobalSections.{u, w} f)

/-- For a scheme X in universe u and c = max(u, w), combine the
delta-functor pullback for id_X with the comparison id_X* ≅ id.
This gives the endomorphism of (RᑫΓ_X) on coefficient sheaves over X. -/
def smallEtaleDerivedGammaIdentityHom (X : Scheme.{u}) :
    smallEtaleGammaDeltaFunctor.{u, w} X ⟶ smallEtaleGammaDeltaFunctor.{u, w} X :=
  smallEtaleDerivedGammaPullbackDeltaHom.{u, w} (𝟙 X) ≫
    CohomologicalDeltaFunctor.precomposeChangeHom
      (smallEtaleInverseImage.{u, w} (𝟙 X)) (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}))
      (smallEtaleDerivedInputShortExact.{u, w} (𝟙 X))
      CohomologicalDeltaFunctor.precomposeIdentityShortExact
      (smallEtaleInverseImageIdIso.{u, w} X).hom (smallEtaleGammaDeltaFunctor.{u, w} X) ≫
    (CohomologicalDeltaFunctor.precomposeIdentityIso (smallEtaleGammaDeltaFunctor.{u, w} X)).hom

@[simp] theorem smallEtaleDerivedGammaIdentityHom_app (X : Scheme.{u}) (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (smallEtaleDerivedGammaIdentityHom.{u, w} X) q =
    smallEtaleDerivedGammaPullback.{u, w} (𝟙 X) q ≫
      Functor.whiskerRight (smallEtaleInverseImageIdIso.{u, w} X).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) ≫
      (Functor.leftUnitor
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).hom := by
  simp only [smallEtaleDerivedGammaIdentityHom, CohomologicalDeltaFunctor.Hom.comp_app,
    CohomologicalDeltaFunctor.precomposeChangeHom_app,
    CohomologicalDeltaFunctor.precomposeIdentityIso_hom_app]
  rfl

/-- For a scheme X in universe u and c = max(u, w), the endomorphism
formed from identity pullback and id_X* ≅ id has degree-zero component
id_(R⁰Γ_X). -/
theorem smallEtaleDerivedGammaIdentityHom_zero (X : Scheme.{u}) :
    CohomologicalDeltaFunctor.Hom.app (smallEtaleDerivedGammaIdentityHom.{u, w} X) 0 =
      𝟙 ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived 0) := by
  rw [smallEtaleDerivedGammaIdentityHom_app]
  apply NatTrans.ext
  funext Q
  let Γ := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let α := (smallEtaleInverseImageIdIso.{u, w} X).hom.app Q
  let z := Γ.rightDerivedZeroIsoSelf
  apply (cancel_mono (z.hom.app Q)).mp
  change ((smallEtaleDerivedGammaPullback.{u, w} (𝟙 X) 0).app Q ≫
      (Γ.rightDerived 0).map α) ≫ z.hom.app Q = 𝟙 _ ≫ z.hom.app Q
  have hn := z.hom.naturality α
  have h0 := congrArg (fun a => a.app Q) (smallEtaleDerivedGammaPullback_zero.{u, w} (𝟙 X))
  have hi := congrArg (fun a => a.app Q) (smallEtalePullbackGlobalSections_id.{u, w} X)
  calc
    _ = (smallEtaleDerivedGammaPullback.{u, w} (𝟙 X) 0).app Q ≫
        (z.hom.app ((smallEtaleInverseImage.{u, w} (𝟙 X)).obj Q) ≫ Γ.map α) :=
      (Category.assoc _ _ _).trans (congrArg (fun a => _ ≫ a) hn)
    _ = (z.hom.app Q ≫ (smallEtalePullbackGlobalSections.{u, w} (𝟙 X)).app Q) ≫ Γ.map α :=
      (Category.assoc _ _ _).symm.trans (congrArg (fun a => a ≫ Γ.map α) h0)
    _ = z.hom.app Q ≫ 𝟙 _ := (Category.assoc _ _ _).trans (congrArg (fun a => z.hom.app Q ≫ a) hi)
    _ = _ := (Category.comp_id _).trans (Category.id_comp _).symm

theorem smallEtaleDerivedGammaIdentityHom_eq (X : Scheme.{u}) :
    smallEtaleDerivedGammaIdentityHom.{u, w} X = 𝟙 (smallEtaleGammaDeltaFunctor.{u, w} X) :=
  CohomologicalDeltaFunctor.hom_eq_of_app_zero (smallEtaleGammaDeltaFunctor.{u, w} X)
    (smallEtaleGammaDeltaFunctor_universal.{u, w} X) (smallEtaleGammaDeltaFunctor.{u, w} X)
    (smallEtaleDerivedGammaIdentityHom.{u, w} X) (𝟙 _) (smallEtaleDerivedGammaIdentityHom_zero.{u, w} X)

/-- For a scheme X in universe u, c = max(u, w), and q ∈ ℕ,
pullback along id_X followed by RᑫΓ_X of id_X*Q ≅ Q is
id_(RᑫΓ_X(Q)). This is the identity law in every nonnegative degree. -/
theorem smallEtaleDerivedGammaPullback_id (X : Scheme.{u}) (q : ℕ) :
    smallEtaleDerivedGammaPullback.{u, w} (𝟙 X) q ≫
      Functor.whiskerRight (smallEtaleInverseImageIdIso.{u, w} X).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    𝟙 ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) := by
  have h := congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (smallEtaleDerivedGammaIdentityHom_eq.{u, w} X)
  rw [smallEtaleDerivedGammaIdentityHom_app] at h
  apply NatTrans.ext
  funext Q
  have hQ := congrArg (fun a => a.app Q) h
  change (((smallEtaleDerivedGammaPullback.{u, w} (𝟙 X) q).app Q ≫
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).map
        ((smallEtaleInverseImageIdIso.{u, w} X).hom.app Q)) ≫
      𝟙 (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).obj Q)) =
    𝟙 (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q).obj Q) at hQ
  exact (Category.comp_id _).symm.trans hQ

end AlgebraicGeometry.Scheme.DerivedSections

end


section

universe u w
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.DerivedSections
local instance smallEtaleCompositionInverseImage_additive {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (smallEtaleInverseImage.{u, w} f).Additive := smallEtaleInverseImage_additive.{u, w} f

/-- For scheme morphisms f : X → Y and g : Y → Z in universe u
and c = max(u, w), compose the delta-functor pullbacks for g and f,
then identify f*g* with (g∘f)*. The result maps
(RᑫΓ_Z) to (Q ↦ RᑫΓ_X((g∘f)*Q)). -/
def smallEtaleDerivedGammaCompositionHom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleGammaDeltaFunctor.{u, w} Z ⟶
      CohomologicalDeltaFunctor.precompose (smallEtaleInverseImage.{u, w} (f ≫ g))
        (smallEtaleDerivedInputShortExact.{u, w} (f ≫ g)) (smallEtaleGammaDeltaFunctor.{u, w} X) := by
  let Lg := smallEtaleInverseImage.{u, w} g
  let Lf := smallEtaleInverseImage.{u, w} f
  let Lc := smallEtaleInverseImage.{u, w} (f ≫ g)
  let hg := smallEtaleDerivedInputShortExact.{u, w} g
  let hf := smallEtaleDerivedInputShortExact.{u, w} f
  let hc := smallEtaleDerivedInputShortExact.{u, w} (f ≫ g)
  let T := smallEtaleGammaDeltaFunctor.{u, w} X
  exact smallEtaleDerivedGammaPullbackDeltaHom.{u, w} g ≫
    (CohomologicalDeltaFunctor.precomposeFunctor Lg hg).map
      (smallEtaleDerivedGammaPullbackDeltaHom.{u, w} f) ≫
    (CohomologicalDeltaFunctor.precomposeCompIso Lg Lf hg hf T).hom ≫
    CohomologicalDeltaFunctor.precomposeChangeHom (Lg ⋙ Lf) Lc
      (CohomologicalDeltaFunctor.precomposeCompShortExact Lg Lf hg hf) hc
      (smallEtaleInverseImageCompIso.{u, w} f g).hom T

@[simp] theorem smallEtaleDerivedGammaCompositionHom_app
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    CohomologicalDeltaFunctor.Hom.app (smallEtaleDerivedGammaCompositionHom.{u, w} f g) q =
    smallEtaleDerivedGammaPullback.{u, w} g q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} g)
        (smallEtaleDerivedGammaPullback.{u, w} f q) ≫
      (Functor.associator (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv ≫
      Functor.whiskerRight (smallEtaleInverseImageCompIso.{u, w} f g).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) := by
  simp only [smallEtaleDerivedGammaCompositionHom, CohomologicalDeltaFunctor.Hom.comp_app]
  rfl

/-- For f : X → Y and g : Y → Z in universe u and c = max(u, w),
the degree-zero composite delta-functor map, under R⁰Γ ≅ Γ,
is the global-section pullback Γ_Z(Q) → Γ_X((g∘f)*Q).
The inverse-image composition comparison is included in this equality. -/
theorem smallEtaleDerivedGammaCompositionHom_zero
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    CohomologicalDeltaFunctor.Hom.app (smallEtaleDerivedGammaCompositionHom.{u, w} f g) 0 ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} (f ≫ g))
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom =
    (Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf.hom ≫
      smallEtalePullbackGlobalSections.{u, w} (f ≫ g) := by
  rw [smallEtaleDerivedGammaCompositionHom_app]
  apply NatTrans.ext
  funext Q
  let Lg := smallEtaleInverseImage.{u, w} g
  let Lf := smallEtaleInverseImage.{u, w} f
  let Lc := smallEtaleInverseImage.{u, w} (f ≫ g)
  let ΓX := Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}
  let ΓY := Sheaf.Γ Y.smallEtaleTopology AddCommGrpCat.{max u w}
  let ΓZ := Sheaf.Γ Z.smallEtaleTopology AddCommGrpCat.{max u w}
  let S := (Lg ⋙ Lf).obj Q
  let R := Lc.obj Q
  let τ := (smallEtaleInverseImageCompIso.{u, w} f g).hom.app Q
  let zX := ΓX.rightDerivedZeroIsoSelf
  let zY := ΓY.rightDerivedZeroIsoSelf
  let zZ := ΓZ.rightDerivedZeroIsoSelf
  let a := (smallEtaleDerivedGammaPullback.{u, w} g 0).app Q
  let b := (smallEtaleDerivedGammaPullback.{u, w} f 0).app (Lg.obj Q)
  change ((a ≫ b) ≫ (ΓX.rightDerived 0).map τ) ≫ zX.hom.app R =
    zZ.hom.app Q ≫ (smallEtalePullbackGlobalSections.{u, w} (f ≫ g)).app Q
  have hn := zX.hom.naturality τ
  change (ΓX.rightDerived 0).map τ ≫ zX.hom.app R = zX.hom.app S ≫ ΓX.map τ at hn
  have hf := congrArg (fun a => a.app (Lg.obj Q)) (smallEtaleDerivedGammaPullback_zero.{u, w} f)
  change b ≫ zX.hom.app S = zY.hom.app (Lg.obj Q) ≫
    (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) at hf
  have hg := congrArg (fun a => a.app Q) (smallEtaleDerivedGammaPullback_zero.{u, w} g)
  change a ≫ zY.hom.app (Lg.obj Q) = zZ.hom.app Q ≫
    (smallEtalePullbackGlobalSections.{u, w} g).app Q at hg
  have hc := congrArg (fun a => a.app Q) (smallEtalePullbackGlobalSections_comp.{u, w} f g)
  change (smallEtalePullbackGlobalSections.{u, w} g).app Q ≫
      (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) ≫ ΓX.map τ =
    (smallEtalePullbackGlobalSections.{u, w} (f ≫ g)).app Q at hc
  calc
    _ = a ≫ b ≫ zX.hom.app S ≫ ΓX.map τ := by
      simpa only [Category.assoc] using congrArg (fun c => (a ≫ b) ≫ c) hn
    _ = a ≫ zY.hom.app (Lg.obj Q) ≫
        (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) ≫ ΓX.map τ := by
      simpa only [Category.assoc] using congrArg (fun c => a ≫ c ≫ ΓX.map τ) hf
    _ = zZ.hom.app Q ≫ (smallEtalePullbackGlobalSections.{u, w} g).app Q ≫
        (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) ≫ ΓX.map τ := by
      simpa only [Category.assoc] using congrArg (fun c => c ≫
        (smallEtalePullbackGlobalSections.{u, w} f).app (Lg.obj Q) ≫ ΓX.map τ) hg
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun c => zZ.hom.app Q ≫ c) hc

theorem smallEtaleDerivedGammaCompositionHom_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    smallEtaleDerivedGammaCompositionHom.{u, w} f g =
      smallEtaleDerivedGammaPullbackDeltaHom.{u, w} (f ≫ g) := by
  apply CohomologicalDeltaFunctor.hom_eq_of_app_zero
    (smallEtaleGammaDeltaFunctor.{u, w} Z) (smallEtaleGammaDeltaFunctor_universal.{u, w} Z)
    (CohomologicalDeltaFunctor.precompose (smallEtaleInverseImage.{u, w} (f ≫ g))
      (smallEtaleDerivedInputShortExact.{u, w} (f ≫ g)) (smallEtaleGammaDeltaFunctor.{u, w} X))
  apply (cancel_mono (Functor.isoWhiskerLeft (smallEtaleInverseImage.{u, w} (f ≫ g))
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerivedZeroIsoSelf).hom).mp
  exact (smallEtaleDerivedGammaCompositionHom_zero.{u, w} f g).trans
    (smallEtaleDerivedGammaPullback_zero.{u, w} (f ≫ g)).symm

/-- For f : X → Y, g : Y → Z in universe u, c = max(u, w), and q ∈ ℕ,
let a_f and a_g be the derived global-section pullbacks and
c_fg : f*g*Q ≅ (g∘f)*Q the inverse-image composition comparison.
Then a_(g∘f)(Q) =
RᑫΓ_X(c_fg) ∘ a_f(g*Q) ∘ a_g(Q).
Thus the map order is pullback along g followed by pullback along f. -/
theorem smallEtaleDerivedGammaPullback_comp
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (q : ℕ) :
    smallEtaleDerivedGammaPullback.{u, w} g q ≫
      Functor.whiskerLeft (smallEtaleInverseImage.{u, w} g)
        (smallEtaleDerivedGammaPullback.{u, w} f q) ≫
      (Functor.associator (smallEtaleInverseImage.{u, w} g) (smallEtaleInverseImage.{u, w} f)
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q)).inv ≫
      Functor.whiskerRight (smallEtaleInverseImageCompIso.{u, w} f g).hom
        ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}).rightDerived q) =
    smallEtaleDerivedGammaPullback.{u, w} (f ≫ g) q := by
  have h := congrArg (fun a => CohomologicalDeltaFunctor.Hom.app a q)
    (smallEtaleDerivedGammaCompositionHom_eq.{u, w} f g)
  rw [smallEtaleDerivedGammaCompositionHom_app] at h
  exact h

end AlgebraicGeometry.Scheme.DerivedSections

end
