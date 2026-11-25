/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Authors: @toskua, Avocado
module
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleDerivedSections
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleLongExactSequenceNaturality
public import MathlibExt.AlgebraicGeometry.Sites.SmallEtaleLongExactSequenceSections
public import MathlibExt.CategoryTheory.Abelian.RightDerived.ResolutionComparison

/-! # Canonical transport of the actual small étale long exact sequence -/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u w v v'

namespace AlgebraicGeometry.Scheme.DerivedSections.CanonicalLongExactSequence

/-- Abelian sheaves on the small étale site of X with values in the common universe. -/
abbrev CommonSheaf (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}

/-- The global sections functor for abelian sheaves on X in the common universe. -/
abbrev gamma (X : Scheme.{u}) :=
  Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}

/-- Small étale cohomology of Q in degree q. -/
abbrev cohomology (X : Scheme.{u}) (Q : CommonSheaf.{u, w} X) (q : ℕ) :=
  Sheaf.H.{max u w, max u w, u, u + 1} Q q

/-- The value on Q of the right derived global sections functor in degree q. -/
abbrev derived (X : Scheme.{u}) (Q : CommonSheaf.{u, w} X) (q : ℕ) :=
  ((gamma.{u, w} X).rightDerived q).obj Q

variable (X : Scheme.{u})

/-- The actual section identification in degree zero, using the existing canonical maps. -/
def zeroEquiv (Q : CommonSheaf.{u, w} X) :
    cohomology.{u, w} X Q 0 ≃+ derived.{u, w} X Q 0 :=
  (smallEtaleH0Sections.{u, w} X Q).trans
    (((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).app Q).addCommGroupIsoToAddEquiv.symm.trans
        (((gamma.{u, w} X).rightDerivedZeroIsoSelf.app Q).addCommGroupIsoToAddEquiv.symm))

theorem zeroEquiv_sections (Q : CommonSheaf.{u, w} X)
    (x : cohomology.{u, w} X Q 0) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).hom.app Q
      (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q)
        (zeroEquiv.{u, w} X Q x)) = smallEtaleH0Sections.{u, w} X Q x := by
  let a0 := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)).app Q |>.addCommGroupIsoToAddEquiv
  let r0 := (gamma.{u, w} X).rightDerivedZeroIsoSelf.app Q |>.addCommGroupIsoToAddEquiv
  change a0 (r0 (r0.symm (a0.symm (smallEtaleH0Sections.{u, w} X Q x)))) = _
  rw [r0.apply_symm_apply, a0.apply_symm_apply]

theorem zeroEquiv_naturality {Q Q' : CommonSheaf.{u, w} X} (f : Q ⟶ Q')
    (x : cohomology.{u, w} X Q 0) :
    zeroEquiv.{u, w} X Q' (Sheaf.H.map f 0 x) =
      ((gamma.{u, w} X).rightDerived 0).map f (zeroEquiv.{u, w} X Q x) := by
  let D := (gamma.{u, w} X).rightDerivedZeroIsoSelf
  let S := Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
    (identityEtaleIsTerminal X)
  apply (D.app Q').addCommGroupIsoToAddEquiv.injective
  apply (S.app Q').addCommGroupIsoToAddEquiv.injective
  change S.hom.app Q' (D.hom.app Q' (zeroEquiv.{u, w} X Q' (Sheaf.H.map f 0 x))) =
    S.hom.app Q' (D.hom.app Q'
      (((gamma.{u, w} X).rightDerived 0).map f (zeroEquiv.{u, w} X Q x)))
  rw [zeroEquiv_sections.{u, w} X Q']
  have hd := ConcreteCategory.congr_hom (D.hom.naturality f) (zeroEquiv.{u, w} X Q x)
  have hs := ConcreteCategory.congr_hom (S.hom.naturality f)
    (D.hom.app Q (zeroEquiv.{u, w} X Q x))
  simp only [ConcreteCategory.comp_apply] at hd hs
  calc
    _ = f.hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (smallEtaleH0Sections.{u, w} X Q x) := smallEtaleH0Sections_naturality X f x
    _ = f.hom.app (op (Scheme.Etale.mk (𝟙 X)))
        (S.hom.app Q (D.hom.app Q (zeroEquiv.{u, w} X Q x))) :=
      congrArg (f.hom.app (op (Scheme.Etale.mk (𝟙 X))))
        (zeroEquiv_sections.{u, w} X Q x).symm
    _ = S.hom.app Q' ((gamma.{u, w} X).map f
        (D.hom.app Q (zeroEquiv.{u, w} X Q x))) := hs.symm
    _ = _ := congrArg (S.hom.app Q') hd.symm

/-- C's internally chosen original cycle presentation, with no supplied certificate. -/
def presentation : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
    (positiveShort.{u, w} X Q n).g.hom.ker →+ cohomology.{u, w} X Q (n + 1) :=
  Classical.choose (positive_ext_original_map_naturality.{u, w} X)

/-- C's unique actual positive comparison family. -/
def positiveEquiv : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
    cohomology.{u, w} X Q (n + 1) ≃+ derived.{u, w} X Q (n + 1) :=
  Classical.choose (Classical.choose_spec (positive_ext_original_map_naturality.{u, w} X))

theorem positiveEquiv_spec :
    positiveExtPacket.{u, w} X (presentation.{u, w} X) (positiveEquiv.{u, w} X) ∧
    (∀ (Q Q' : CommonSheaf.{u, w} X) (τ : Q ⟶ Q') (n : ℕ)
      (x : cohomology.{u, w} X Q (n + 1)),
      positiveEquiv.{u, w} X Q' n (Sheaf.H.map τ (n + 1) x) =
        ((gamma.{u, w} X).rightDerived (n + 1)).map τ (positiveEquiv.{u, w} X Q n x)) ∧
    ∀ p e, positiveExtPacket.{u, w} X p e → e = positiveEquiv.{u, w} X :=
  Classical.choose_spec
    (Classical.choose_spec (positive_ext_original_map_naturality.{u, w} X))

/-- One common-universe family, with the actual section map at zero and C's family thereafter. -/
def canonicalEquiv (Q : CommonSheaf.{u, w} X) (q : ℕ) :
    cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q :=
  match q with
  | 0 => zeroEquiv.{u, w} X Q
  | n + 1 => positiveEquiv.{u, w} X Q n

theorem canonicalEquiv_positive_packet :
    positiveExtPacket.{u, w} X (presentation.{u, w} X)
      (fun Q n => canonicalEquiv.{u, w} X Q (n + 1)) :=
  (positiveEquiv_spec.{u, w} X).1

theorem canonicalEquiv_zero_sections (Q : CommonSheaf.{u, w} X)
    (x : cohomology.{u, w} X Q 0) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).hom.app Q
      (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q)
        (canonicalEquiv.{u, w} X Q 0 x)) = smallEtaleH0Sections.{u, w} X Q x :=
  zeroEquiv_sections.{u, w} X Q x

theorem canonicalEquiv_naturality {Q Q' : CommonSheaf.{u, w} X} (τ : Q ⟶ Q')
    (q : ℕ) (x : cohomology.{u, w} X Q q) :
    canonicalEquiv.{u, w} X Q' q (Sheaf.H.map τ q x) =
      ((gamma.{u, w} X).rightDerived q).map τ (canonicalEquiv.{u, w} X Q q x) := by
  cases q with
  | zero => exact zeroEquiv_naturality.{u, w} X τ x
  | succ n => exact (positiveEquiv_spec.{u, w} X).2.1 Q Q' τ n x

theorem canonicalEquiv_unique
    (e : ∀ (Q : CommonSheaf.{u, w} X) (q : ℕ),
      cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q)
    (h0 : ∀ (Q : CommonSheaf.{u, w} X) (x : cohomology.{u, w} X Q 0),
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
        (identityEtaleIsTerminal X)).hom.app Q
        (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q) (e Q 0 x)) =
          smallEtaleH0Sections.{u, w} X Q x)
    (p : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
      (positiveShort.{u, w} X Q n).g.hom.ker →+ cohomology.{u, w} X Q (n + 1))
    (hp : positiveExtPacket.{u, w} X p (fun Q n => e Q (n + 1))) :
    e = canonicalEquiv.{u, w} X := by
  have hpos := (positiveEquiv_spec.{u, w} X).2.2 p (fun Q n => e Q (n + 1)) hp
  funext Q q
  cases q with
  | zero =>
      apply DFunLike.coe_injective
      funext x
      apply ((gamma.{u, w} X).rightDerivedZeroIsoSelf.app Q).addCommGroupIsoToAddEquiv.injective
      apply ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
        (identityEtaleIsTerminal X)).app Q).addCommGroupIsoToAddEquiv.injective
      exact (h0 Q x).trans (canonicalEquiv_zero_sections.{u, w} X Q x).symm
  | succ n => exact congrFun (congrFun hpos Q) n

theorem canonicalEquiv_representative (Q : CommonSheaf.{u, w} X) (n : ℕ)
    (f : integralSheaf.{u, w} X ⟶ (injectiveResolution Q).cocomplex.X (n + 1))
    (hf : f ≫ (injectiveResolution Q).cocomplex.d (n + 1) (n + 2) = 0) :
    ∃ z : (positiveShort.{u, w} X Q n).g.hom.ker,
      z.val = integralHomSections.{u, w} X _ f ∧
      canonicalEquiv.{u, w} X Q (n + 1)
        ((injectiveResolution Q).extMk f (n + 2) rfl hf) =
          positiveCycleClass.{u, w} X Q n z := by
  obtain ⟨z, hz, hp⟩ := ((canonicalEquiv_positive_packet.{u, w} X) Q n).2.2.2 f hf
  refine ⟨z, hz, ?_⟩
  rw [← hp]
  exact ((canonicalEquiv_positive_packet.{u, w} X) Q n).2.2.1 z

/-- The canonical isomorphism from small étale cohomology to derived global sections. -/
def comparisonIso (Q : CommonSheaf.{u, w} X) (q : ℕ) :
    AddCommGrpCat.of (cohomology.{u, w} X Q q) ≅ derived.{u, w} X Q q :=
  (canonicalEquiv.{u, w} X Q q).toAddCommGrpIso

@[reassoc]
theorem comparisonIso_naturality {Q Q' : CommonSheaf.{u, w} X} (τ : Q ⟶ Q') (q : ℕ) :
    AddCommGrpCat.ofHom (Sheaf.H.map τ q) ≫ (comparisonIso.{u, w} X Q' q).hom =
      (comparisonIso.{u, w} X Q q).hom ≫ ((gamma.{u, w} X).rightDerived q).map τ := by
  ext x
  exact canonicalEquiv_naturality.{u, w} X τ q x

theorem canonicalEquiv_symm_naturality {Q Q' : CommonSheaf.{u, w} X} (τ : Q ⟶ Q')
    (q : ℕ) (x : derived.{u, w} X Q q) :
    (canonicalEquiv.{u, w} X Q' q).symm (((gamma.{u, w} X).rightDerived q).map τ x) =
      Sheaf.H.map τ q ((canonicalEquiv.{u, w} X Q q).symm x) := by
  apply (canonicalEquiv.{u, w} X Q' q).injective
  rw [AddEquiv.apply_symm_apply, canonicalEquiv_naturality, AddEquiv.apply_symm_apply]

variable {X}
  {S T : ShortComplex (CommonSheaf.{u, w} X)}

/-- Explicit canonical transport of the same intrinsic extension-class boundary. -/
def derivedBoundary (hS : S.ShortExact) (n : ℕ) :
    derived.{u, w} X S.X₃ n →+ derived.{u, w} X S.X₁ (n + 1) :=
  (canonicalEquiv.{u, w} X S.X₁ (n + 1)).toAddMonoidHom.comp
    ((smallEtaleConnectingMap.{u, w} hS n).comp
      (canonicalEquiv.{u, w} X S.X₃ n).symm.toAddMonoidHom)

theorem derivedBoundary_comparison (hS : S.ShortExact) (n : ℕ)
    (x : cohomology.{u, w} X S.X₃ n) :
    derivedBoundary.{u, w} hS n (canonicalEquiv.{u, w} X S.X₃ n x) =
      canonicalEquiv.{u, w} X S.X₁ (n + 1) (smallEtaleConnectingMap.{u, w} hS n x) := by
  change canonicalEquiv.{u, w} X S.X₁ (n + 1)
    (smallEtaleConnectingMap.{u, w} hS n
      ((canonicalEquiv.{u, w} X S.X₃ n).symm (canonicalEquiv.{u, w} X S.X₃ n x))) = _
  rw [AddEquiv.symm_apply_apply]

theorem derivedBoundary_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (α : S ⟶ T) (n : ℕ) (x : derived.{u, w} X S.X₃ n) :
    derivedBoundary.{u, w} hT n (((gamma.{u, w} X).rightDerived n).map α.τ₃ x) =
      ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₁ (derivedBoundary.{u, w} hS n x) := by
  change canonicalEquiv.{u, w} X T.X₁ (n + 1)
      (smallEtaleConnectingMap.{u, w} hT n
        ((canonicalEquiv.{u, w} X T.X₃ n).symm
          (((gamma.{u, w} X).rightDerived n).map α.τ₃ x))) = _
  rw [canonicalEquiv_symm_naturality, smallEtaleConnectingMap_naturality,
    canonicalEquiv_naturality]
  rfl

/-- The literal actual right-derived maps in every adjacent-degree window. -/
def derivedSequence (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{max u w} 5 :=
  ComposableArrows.mk₅ (((gamma.{u, w} X).rightDerived n).map S.f)
    (((gamma.{u, w} X).rightDerived n).map S.g)
    (AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n))
    (((gamma.{u, w} X).rightDerived (n + 1)).map S.f)
    (((gamma.{u, w} X).rightDerived (n + 1)).map S.g)

/-- Compare the windows of five arrows for small étale cohomology and derived global sections
in degrees n and n + 1. -/
def sequenceComparison (hS : S.ShortExact) (n : ℕ) :
    smallEtaleLongSequence.{u, w} hS n ≅ derivedSequence.{u, w} hS n := by
  refine ComposableArrows.isoMk₅ (comparisonIso.{u, w} X S.X₁ n)
    (comparisonIso.{u, w} X S.X₂ n) (comparisonIso.{u, w} X S.X₃ n)
    (comparisonIso.{u, w} X S.X₁ (n + 1)) (comparisonIso.{u, w} X S.X₂ (n + 1))
    (comparisonIso.{u, w} X S.X₃ (n + 1)) ?_ ?_ ?_ ?_ ?_
  · exact comparisonIso_naturality.{u, w} X S.f n
  · exact comparisonIso_naturality.{u, w} X S.g n
  · ext x
    exact (derivedBoundary_comparison.{u, w} hS n x).symm
  · exact comparisonIso_naturality.{u, w} X S.f (n + 1)
  · exact comparisonIso_naturality.{u, w} X S.g (n + 1)

theorem derivedSequence_exact (hS : S.ShortExact) (n : ℕ) :
    (derivedSequence.{u, w} hS n).Exact :=
  ComposableArrows.exact_of_iso (sequenceComparison.{u, w} hS n)
    (smallEtaleLongSequence_exact.{u, w} hS n)

theorem derivedSequence_initial_injective (hS : S.ShortExact) :
    Function.Injective (((gamma.{u, w} X).rightDerived 0).map S.f) := by
  intro a b hab
  apply (canonicalEquiv.{u, w} X S.X₁ 0).symm.injective
  apply smallEtaleLongSequence_initial_injective hS
  rw [← canonicalEquiv_symm_naturality, ← canonicalEquiv_symm_naturality, hab]

/-- The morphism between windows of derived global sections induced by a morphism
of short exact sequences. -/
def derivedSequenceHom (hS : S.ShortExact) (hT : T.ShortExact) (α : S ⟶ T) (n : ℕ) :
    derivedSequence.{u, w} hS n ⟶ derivedSequence.{u, w} hT n := by
  refine ComposableArrows.homMk₅ (((gamma.{u, w} X).rightDerived n).map α.τ₁)
    (((gamma.{u, w} X).rightDerived n).map α.τ₂)
    (((gamma.{u, w} X).rightDerived n).map α.τ₃)
    (((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₁)
    (((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₂)
    (((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₃) ?_ ?_ ?_ ?_ ?_
  · change ((gamma.{u, w} X).rightDerived n).map S.f ≫
      ((gamma.{u, w} X).rightDerived n).map α.τ₂ =
        ((gamma.{u, w} X).rightDerived n).map α.τ₁ ≫
          ((gamma.{u, w} X).rightDerived n).map T.f
    exact (((gamma.{u, w} X).rightDerived n).map_comp S.f α.τ₂).symm.trans
      ((congrArg ((gamma.{u, w} X).rightDerived n).map α.comm₁₂.symm).trans
        (((gamma.{u, w} X).rightDerived n).map_comp α.τ₁ T.f))
  · change ((gamma.{u, w} X).rightDerived n).map S.g ≫
      ((gamma.{u, w} X).rightDerived n).map α.τ₃ =
        ((gamma.{u, w} X).rightDerived n).map α.τ₂ ≫
          ((gamma.{u, w} X).rightDerived n).map T.g
    exact (((gamma.{u, w} X).rightDerived n).map_comp S.g α.τ₃).symm.trans
      ((congrArg ((gamma.{u, w} X).rightDerived n).map α.comm₂₃.symm).trans
        (((gamma.{u, w} X).rightDerived n).map_comp α.τ₂ T.g))
  · ext x
    exact (derivedBoundary_naturality.{u, w} hS hT α n x).symm
  · change ((gamma.{u, w} X).rightDerived (n + 1)).map S.f ≫
      ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₂ =
        ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₁ ≫
          ((gamma.{u, w} X).rightDerived (n + 1)).map T.f
    exact (((gamma.{u, w} X).rightDerived (n + 1)).map_comp S.f α.τ₂).symm.trans
      ((congrArg ((gamma.{u, w} X).rightDerived (n + 1)).map α.comm₁₂.symm).trans
        (((gamma.{u, w} X).rightDerived (n + 1)).map_comp α.τ₁ T.f))
  · change ((gamma.{u, w} X).rightDerived (n + 1)).map S.g ≫
      ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₃ =
        ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₂ ≫
          ((gamma.{u, w} X).rightDerived (n + 1)).map T.g
    exact (((gamma.{u, w} X).rightDerived (n + 1)).map_comp S.g α.τ₃).symm.trans
      ((congrArg ((gamma.{u, w} X).rightDerived (n + 1)).map α.comm₂₃.symm).trans
        (((gamma.{u, w} X).rightDerived (n + 1)).map_comp α.τ₂ T.g))

/-- Assign each short exact sequence its window of five arrows for derived global sections
in degrees n and n + 1. -/
def derivedSequenceFunctor (X : Scheme.{u}) (n : ℕ) :
    ShortExactSequence (CommonSheaf.{u, w} X) ⥤ ComposableArrows AddCommGrpCat.{max u w} 5 where
  obj S := derivedSequence.{u, w} S.property n
  map α := derivedSequenceHom.{u, w} _ _ α.hom n
  map_id S := by
    apply ComposableArrows.hom_ext₅
    · exact ((gamma.{u, w} X).rightDerived n).map_id S.obj.X₁
    · exact ((gamma.{u, w} X).rightDerived n).map_id S.obj.X₂
    · exact ((gamma.{u, w} X).rightDerived n).map_id S.obj.X₃
    · exact ((gamma.{u, w} X).rightDerived (n + 1)).map_id S.obj.X₁
    · exact ((gamma.{u, w} X).rightDerived (n + 1)).map_id S.obj.X₂
    · exact ((gamma.{u, w} X).rightDerived (n + 1)).map_id S.obj.X₃
  map_comp α β := by
    apply ComposableArrows.hom_ext₅
    · exact ((gamma.{u, w} X).rightDerived n).map_comp α.hom.τ₁ β.hom.τ₁
    · exact ((gamma.{u, w} X).rightDerived n).map_comp α.hom.τ₂ β.hom.τ₂
    · exact ((gamma.{u, w} X).rightDerived n).map_comp α.hom.τ₃ β.hom.τ₃
    · exact ((gamma.{u, w} X).rightDerived (n + 1)).map_comp α.hom.τ₁ β.hom.τ₁
    · exact ((gamma.{u, w} X).rightDerived (n + 1)).map_comp α.hom.τ₂ β.hom.τ₂
    · exact ((gamma.{u, w} X).rightDerived (n + 1)).map_comp α.hom.τ₃ β.hom.τ₃

/-- The natural comparison between the small étale and derived global sections sequence functors. -/
def sequenceComparisonNatIso (X : Scheme.{u}) (n : ℕ) :
    smallEtaleLongSequenceFunctor.{u, w} X n ≅ derivedSequenceFunctor.{u, w} X n :=
  NatIso.ofComponents (fun S => sequenceComparison.{u, w} S.property n) (by
    intro S T α
    apply ComposableArrows.hom_ext₅
    · exact comparisonIso_naturality.{u, w} X α.hom.τ₁ n
    · exact comparisonIso_naturality.{u, w} X α.hom.τ₂ n
    · exact comparisonIso_naturality.{u, w} X α.hom.τ₃ n
    · exact comparisonIso_naturality.{u, w} X α.hom.τ₁ (n + 1)
    · exact comparisonIso_naturality.{u, w} X α.hom.τ₂ (n + 1)
    · exact comparisonIso_naturality.{u, w} X α.hom.τ₃ (n + 1))

/-- The six components are precisely the same original right-derived morphism maps. -/
def DerivedSequenceComponents (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (CommonSheaf.{u, w} X)} (α : S ⟶ T) : Prop :=
  let m := (derivedSequenceFunctor.{u, w} X n).map α
  m.app 0 = ((gamma.{u, w} X).rightDerived n).map α.hom.τ₁ ∧
  m.app 1 = ((gamma.{u, w} X).rightDerived n).map α.hom.τ₂ ∧
  m.app 2 = ((gamma.{u, w} X).rightDerived n).map α.hom.τ₃ ∧
  m.app 3 = ((gamma.{u, w} X).rightDerived (n + 1)).map α.hom.τ₁ ∧
  m.app 4 = ((gamma.{u, w} X).rightDerived (n + 1)).map α.hom.τ₂ ∧
  m.app 5 = ((gamma.{u, w} X).rightDerived (n + 1)).map α.hom.τ₃

theorem derivedSequenceFunctor_components (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (CommonSheaf.{u, w} X)} (α : S ⟶ T) :
    DerivedSequenceComponents.{u, w} X n α := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem conjugate_boundary_comparison {C : Type v} [Category.{v'} C]
    {A A' B B' U V : C} (eA : U ≅ A) (eA' : U ≅ A') (eB : V ≅ B) (eB' : V ≅ B')
    (δ : U ⟶ V) :
    (eA.inv ≫ δ ≫ eB.hom) ≫ (eB.symm.trans eB').hom =
      (eA.symm.trans eA').hom ≫ (eA'.inv ≫ δ ≫ eB'.hom) := by
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.hom_inv_id_assoc]

private theorem conjugate_boundary_naturality {C : Type v} [Category.{v'} C]
    {A A' B B' U U' V V' : C} (eA : U ≅ A) (eA' : U' ≅ A')
    (eB : V ≅ B) (eB' : V' ≅ B') (δ : U ⟶ V) (δ' : U' ⟶ V')
    (a : U ⟶ U') (b : V ⟶ V') (a' : A ⟶ A') (b' : B ⟶ B')
    (hA : eA.inv ≫ a = a' ≫ eA'.inv) (hB : b ≫ eB'.hom = eB.hom ≫ b')
    (hδ : δ ≫ b = a ≫ δ') :
    (eA.inv ≫ δ ≫ eB.hom) ≫ b' = a' ≫ (eA'.inv ≫ δ' ≫ eB'.hom) := by
  simp only [Category.assoc]
  rw [← hB, reassoc_of% hδ, reassoc_of% hA]

/-- Literal Gamma-resolution homology, without a new quotient or homology construction. -/
abbrev resolutionHomology (X : Scheme.{u}) {Q : CommonSheaf.{u, w} X}
    (R : InjectiveResolution Q) (q : ℕ) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u w} (ComplexShape.up ℕ) q).obj
    (((gamma.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex)

/-- The connecting map between homology groups of the global sections of the chosen endpoint
injective resolutions, obtained by conjugating the derived boundary with their comparison
isomorphisms. -/
def resolutionBoundary (hS : S.ShortExact) (n : ℕ)
    (R₁ : InjectiveResolution S.X₁) (R₃ : InjectiveResolution S.X₃) :
    resolutionHomology.{u, w} X R₃ n ⟶ resolutionHomology.{u, w} X R₁ (n + 1) :=
  (R₃.isoRightDerivedObj (gamma.{u, w} X) n).inv ≫
    AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n) ≫
      (R₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1)).hom

theorem resolutionBoundary_comparison (hS : S.ShortExact) (n : ℕ)
    (R₁ J₁ : InjectiveResolution S.X₁) (R₃ J₃ : InjectiveResolution S.X₃) :
    resolutionBoundary.{u, w} hS n R₁ R₃ ≫
        (InjectiveResolution.cohomologyComparisonIso R₁ J₁ (gamma.{u, w} X) (n + 1)).hom =
      (InjectiveResolution.cohomologyComparisonIso R₃ J₃ (gamma.{u, w} X) n).hom ≫
        resolutionBoundary.{u, w} hS n J₁ J₃ := by
  exact conjugate_boundary_comparison (R₃.isoRightDerivedObj (gamma.{u, w} X) n)
    (J₃.isoRightDerivedObj (gamma.{u, w} X) n)
    (R₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1))
    (J₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1))
    (AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n))

/-- The homology map induced by applying global sections to a comparison of
injective resolutions. -/
abbrev resolutionMap {Q Q' : CommonSheaf.{u, w} X} {R : InjectiveResolution Q}
    {R' : InjectiveResolution Q'} {τ : Q ⟶ Q'} (φ : R.Hom R' τ) (q : ℕ) :=
  ((gamma.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u w} (ComplexShape.up ℕ) q).map φ.hom

/-- Every actual cochain comparison over every original sequence morphism commutes with δ. -/
theorem resolutionBoundary_naturality (hS : S.ShortExact) (hT : T.ShortExact)
    (α : S ⟶ T) (n : ℕ)
    {R₁ : InjectiveResolution S.X₁} {R₃ : InjectiveResolution S.X₃}
    {J₁ : InjectiveResolution T.X₁} {J₃ : InjectiveResolution T.X₃}
    (φ₁ : R₁.Hom J₁ α.τ₁) (φ₃ : R₃.Hom J₃ α.τ₃) :
    resolutionBoundary.{u, w} hS n R₁ R₃ ≫ resolutionMap.{u, w} φ₁ (n + 1) =
      resolutionMap.{u, w} φ₃ n ≫ resolutionBoundary.{u, w} hT n J₁ J₃ := by
  have h₁ : ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₁ ≫
      (J₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1)).hom =
    (R₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1)).hom ≫ resolutionMap.{u, w} φ₁ (n + 1) := by
    rw [(gamma.{u, w} X).rightDerived_map_eq (n + 1) α.τ₁ φ₁.hom φ₁.ι_comp_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  have h₃ : (R₃.isoRightDerivedObj (gamma.{u, w} X) n).inv ≫
      ((gamma.{u, w} X).rightDerived n).map α.τ₃ =
    resolutionMap.{u, w} φ₃ n ≫ (J₃.isoRightDerivedObj (gamma.{u, w} X) n).inv := by
    rw [(gamma.{u, w} X).rightDerived_map_eq n α.τ₃ φ₃.hom φ₃.ι_comp_hom]
    simp only [Iso.inv_hom_id_assoc]
  have hδ : AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n) ≫
      ((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₁ =
    ((gamma.{u, w} X).rightDerived n).map α.τ₃ ≫
      AddCommGrpCat.ofHom (derivedBoundary.{u, w} hT n) := by
    ext x
    exact (derivedBoundary_naturality.{u, w} hS hT α n x).symm
  exact conjugate_boundary_naturality (R₃.isoRightDerivedObj (gamma.{u, w} X) n)
    (J₃.isoRightDerivedObj (gamma.{u, w} X) n)
    (R₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1))
    (J₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1))
    (AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n))
    (AddCommGrpCat.ofHom (derivedBoundary.{u, w} hT n))
    (((gamma.{u, w} X).rightDerived n).map α.τ₃)
    (((gamma.{u, w} X).rightDerived (n + 1)).map α.τ₁)
    (resolutionMap.{u, w} φ₃ n) (resolutionMap.{u, w} φ₁ (n + 1)) h₃ h₁ hδ

/-- A parent family with the original q0 and full positive laws is the restriction of this E. -/
theorem original_family_agreement
    (eo : ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{w}) (q : ℕ),
      cohomology.{u, w} X ((liftCoefficients.{u, w} X).obj F) q ≃+
        derived.{u, w} X ((liftCoefficients.{u, w} X).obj F) q)
    (h0 : ∀ F (x : cohomology.{u, w} X ((liftCoefficients.{u, w} X).obj F) 0),
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
        (identityEtaleIsTerminal X)).hom.app ((liftCoefficients.{u, w} X).obj F)
        (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app ((liftCoefficients.{u, w} X).obj F))
          (eo F 0 x)) = smallEtaleH0Sections.{u, w} X ((liftCoefficients.{u, w} X).obj F) x)
    (p : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
      (positiveShort.{u, w} X Q n).g.hom.ker →+ cohomology.{u, w} X Q (n + 1))
    (ep : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
      cohomology.{u, w} X Q (n + 1) ≃+ derived.{u, w} X Q (n + 1))
    (hp : positiveExtPacket.{u, w} X p ep)
    (hsucc : ∀ F n, eo F (n + 1) = ep ((liftCoefficients.{u, w} X).obj F) n) :
    ∀ F q, eo F q = canonicalEquiv.{u, w} X ((liftCoefficients.{u, w} X).obj F) q := by
  have hpos := (positiveEquiv_spec.{u, w} X).2.2 p ep hp
  intro F q
  cases q with
  | zero =>
      apply DFunLike.coe_injective
      funext x
      apply ((gamma.{u, w} X).rightDerivedZeroIsoSelf.app
        ((liftCoefficients.{u, w} X).obj F)).addCommGroupIsoToAddEquiv.injective
      let A := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
        (identityEtaleIsTerminal X)).app ((liftCoefficients.{u, w} X).obj F)
      apply A.addCommGroupIsoToAddEquiv.injective
      exact (h0 F x).trans
        (canonicalEquiv_zero_sections.{u, w} X ((liftCoefficients.{u, w} X).obj F) x).symm
  | succ n => exact (hsucc F n).trans (congrFun (congrFun hpos _) n)

/-- The exact original zero and positive laws that force the all-degree family. -/
def CanonicalFamily (X : Scheme.{u})
    (e : ∀ (Q : CommonSheaf.{u, w} X) (q : ℕ),
      cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q) : Prop :=
  (∀ (Q : CommonSheaf.{u, w} X) (x : cohomology.{u, w} X Q 0),
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).hom.app Q
      (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q) (e Q 0 x)) =
        smallEtaleH0Sections.{u, w} X Q x) ∧
  ∃ p, positiveExtPacket.{u, w} X p (fun Q n => e Q (n + 1))

theorem canonicalFamily_unique (X : Scheme.{u})
    (e : ∀ (Q : CommonSheaf.{u, w} X) (q : ℕ),
      cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q)
    (h : CanonicalFamily.{u, w} X e) : e = canonicalEquiv.{u, w} X := by
  obtain ⟨p, hp⟩ := h.2
  exact canonicalEquiv_unique.{u, w} X e h.1 p hp

/-- Full original sequence functor laws and all actual components and squares. -/
def DerivedFunctorLaws (X : Scheme.{u}) (n : ℕ) : Prop :=
  let F := derivedSequenceFunctor.{u, w} X n
  (∀ (S T : ShortExactSequence (CommonSheaf.{u, w} X)) (α : S ⟶ T),
    DerivedSequenceComponents.{u, w} X n α) ∧
  (∀ (S T : ShortExactSequence (CommonSheaf.{u, w} X)) (α : S ⟶ T)
    (i j : Fin 6) (h : i ≤ j),
    (F.obj S).map (homOfLE h) ≫ (F.map α).app j =
      (F.map α).app i ≫ (F.obj T).map (homOfLE h)) ∧
  (∀ S, F.map (𝟙 S) = 𝟙 (F.obj S)) ∧
  ∀ (S T U : ShortExactSequence (CommonSheaf.{u, w} X)) (α : S ⟶ T) (β : T ⟶ U),
    F.map (α ≫ β) = F.map α ≫ F.map β

theorem derivedFunctorLaws (X : Scheme.{u}) (n : ℕ) : DerivedFunctorLaws.{u, w} X n :=
  ⟨fun _ _ α => derivedSequenceFunctor_components.{u, w} X n α,
    fun _ _ α _ _ h => ((derivedSequenceFunctor.{u, w} X n).map α).naturality (homOfLE h),
    (derivedSequenceFunctor.{u, w} X n).map_id,
    fun _ _ _ α β => (derivedSequenceFunctor.{u, w} X n).map_comp α β⟩

/-- Complete literal right-derived LES, original class laws, natural comparison
and resolution square. -/
theorem original_small_etale_derived_long_exact_sequence (X : Scheme.{u}) :
    positiveExtPacket.{u, w} X (presentation.{u, w} X)
      (fun Q n => canonicalEquiv.{u, w} X Q (n + 1)) ∧
    (∀ (Q : CommonSheaf.{u, w} X) (x : cohomology.{u, w} X Q 0),
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
        (identityEtaleIsTerminal X)).hom.app Q
        (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q)
          (canonicalEquiv.{u, w} X Q 0 x)) = smallEtaleH0Sections.{u, w} X Q x) ∧
    (∀ (Q Q' : CommonSheaf.{u, w} X) (τ : Q ⟶ Q') (q : ℕ) (x : cohomology.{u, w} X Q q),
      canonicalEquiv.{u, w} X Q' q (Sheaf.H.map τ q x) =
        ((gamma.{u, w} X).rightDerived q).map τ (canonicalEquiv.{u, w} X Q q x)) ∧
    (∀ (S : ShortComplex (CommonSheaf.{u, w} X)) (hS : S.ShortExact) (n : ℕ),
      (derivedSequence.{u, w} hS n).Exact) ∧
    (∀ (S : ShortComplex (CommonSheaf.{u, w} X)) (_hS : S.ShortExact),
      Function.Injective (((gamma.{u, w} X).rightDerived 0).map S.f)) ∧
    (∀ n, DerivedFunctorLaws.{u, w} X n) ∧
    (∀ (e : ∀ (Q : CommonSheaf.{u, w} X) (q : ℕ),
      cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q),
      CanonicalFamily.{u, w} X e → e = canonicalEquiv.{u, w} X) ∧
    (∀ (S : ShortComplex (CommonSheaf.{u, w} X)) (hS : S.ShortExact) (n : ℕ)
      (x : cohomology.{u, w} X S.X₃ n),
      derivedBoundary.{u, w} hS n (canonicalEquiv.{u, w} X S.X₃ n x) =
        canonicalEquiv.{u, w} X S.X₁ (n + 1) (smallEtaleConnectingMap.{u, w} hS n x)) ∧
    (∀ n (S T : ShortExactSequence (CommonSheaf.{u, w} X)) (α : S ⟶ T),
      (smallEtaleLongSequenceFunctor.{u, w} X n).map α ≫
          (sequenceComparisonNatIso.{u, w} X n).hom.app T =
        (sequenceComparisonNatIso.{u, w} X n).hom.app S ≫
          (derivedSequenceFunctor.{u, w} X n).map α) ∧
    (∀ (S : ShortComplex (CommonSheaf.{u, w} X)) (hS : S.ShortExact) (n : ℕ)
      (R₁ J₁ : InjectiveResolution S.X₁) (R₃ J₃ : InjectiveResolution S.X₃),
      resolutionBoundary.{u, w} hS n R₁ R₃ ≫
          (InjectiveResolution.cohomologyComparisonIso R₁ J₁ (gamma.{u, w} X) (n + 1)).hom =
        (InjectiveResolution.cohomologyComparisonIso R₃ J₃ (gamma.{u, w} X) n).hom ≫
          resolutionBoundary.{u, w} hS n J₁ J₃) ∧
    ∀ (S T : ShortComplex (CommonSheaf.{u, w} X)) (hS : S.ShortExact) (hT : T.ShortExact)
      (α : S ⟶ T) (n : ℕ)
      (R₁ : InjectiveResolution S.X₁) (R₃ : InjectiveResolution S.X₃)
      (J₁ : InjectiveResolution T.X₁) (J₃ : InjectiveResolution T.X₃)
      (φ₁ : R₁.Hom J₁ α.τ₁) (φ₃ : R₃.Hom J₃ α.τ₃),
      resolutionBoundary.{u, w} hS n R₁ R₃ ≫ resolutionMap.{u, w} φ₁ (n + 1) =
        resolutionMap.{u, w} φ₃ n ≫ resolutionBoundary.{u, w} hT n J₁ J₃ := by
  exact ⟨canonicalEquiv_positive_packet.{u, w} X, canonicalEquiv_zero_sections.{u, w} X,
    fun _ _ τ q x => canonicalEquiv_naturality.{u, w} X τ q x,
    fun _ hS n => derivedSequence_exact.{u, w} hS n,
    fun _ hS => derivedSequence_initial_injective.{u, w} hS,
    derivedFunctorLaws.{u, w} X, canonicalFamily_unique.{u, w} X,
    fun _ hS n x => derivedBoundary_comparison.{u, w} hS n x,
    fun n _ _ α => (sequenceComparisonNatIso.{u, w} X n).hom.naturality α,
    fun _ hS n R₁ J₁ R₃ J₃ => resolutionBoundary_comparison.{u, w} hS n R₁ J₁ R₃ J₃,
    fun _ _ hS hT α n _ _ _ _ φ₁ φ₃ => resolutionBoundary_naturality.{u, w} hS hT α n φ₁ φ₃⟩


end AlgebraicGeometry.Scheme.DerivedSections.CanonicalLongExactSequence
