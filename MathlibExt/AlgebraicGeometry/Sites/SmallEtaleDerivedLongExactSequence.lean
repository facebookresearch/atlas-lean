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

/-!
# Cohomology comparisons and derived section exact sequences

For a scheme `X : Scheme.{u}`, use abelian sheaves with coefficient universe `λ = max u w`.
Their small étale cohomology groups compare with `R^qΓ` in every natural degree. In degree
zero the coordinate is evaluation on the identity étale object. In positive degrees it is
determined by closed integral-sheaf maps into an injective resolution, with the section cycles
quotiented by boundaries.

Transport the cohomological connecting map through these comparisons to obtain `R^nΓ(S₃) →
R^(n+1)Γ(S₁)` for each short exact sequence. The resulting six-term windows are exact, natural
in sequence morphisms, and have an injective first map in degree zero.

Injective-resolution coordinates give the same boundary after changing resolutions and commute
with resolution maps over sequence morphisms. The section and representative normalizations
uniquely determine the comparison family.
-/
@[expose] public section
noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
universe u w v v'

namespace AlgebraicGeometry.Scheme.DerivedSections.CanonicalLongExactSequence

/-- Abelian sheaves in the common coefficient universe.

For `X : Scheme.{u}`, these are sheaves on `X.smallEtaleTopology` with values in additive
groups of universe `max u w`. -/
abbrev CommonSheaf (X : Scheme.{u}) :=
  Sheaf X.smallEtaleTopology AddCommGrpCat.{max u w}

/-- Global sections in the common coefficient universe.

The functor `gamma X` is `Sheaf.Γ` for the small étale topology with additive-group
coefficients in universe `max u w`. -/
abbrev gamma (X : Scheme.{u}) :=
  Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{max u w}

/-- Small étale cohomology in a fixed natural degree.

For a common-universe sheaf `Q`, `cohomology X Q q` is its small étale cohomology group
`Sheaf.H Q q` in natural degree `q`. -/
abbrev cohomology (X : Scheme.{u}) (Q : CommonSheaf.{u, w} X) (q : ℕ) :=
  Sheaf.H.{max u w, max u w, u, u + 1} Q q

/-- Right derived global sections in a fixed natural degree.

For a common-universe sheaf `Q`, evaluate the degree-`q` right-derived global-sections functor
at `Q`. -/
abbrev derived (X : Scheme.{u}) (Q : CommonSheaf.{u, w} X) (q : ℕ) :=
  ((gamma.{u, w} X).rightDerived q).obj Q

variable (X : Scheme.{u})

/-- Degree zero comparison from cohomology to derived sections.

Identify `H⁰(X,Q)` with sections on the identity étale object, then with global sections, and
then with degree-zero right-derived global sections. -/
def zeroEquiv (Q : CommonSheaf.{u, w} X) :
    cohomology.{u, w} X Q 0 ≃+ derived.{u, w} X Q 0 :=
  (smallEtaleH0Sections.{u, w} X Q).trans
    (((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).app Q).addCommGroupIsoToAddEquiv.symm.trans
        (((gamma.{u, w} X).rightDerivedZeroIsoSelf.app Q).addCommGroupIsoToAddEquiv.symm))

/-- Degree zero comparison preserves terminal section values.

The degree-zero comparison followed by the derived-zero global-sections coordinate and
terminal-object evaluation equals the degree-zero cohomology section coordinate. -/
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

/-- Degree zero comparison is natural in sheaf maps.

For a sheaf morphism, its degree-zero cohomology map commutes with the comparison to the
degree-zero right-derived global-sections map. -/
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

/-- Positive cohomology classes from resolution section cycles.

For degree `n + 1`, the presentation is an additive map from the kernel of the outgoing
global-section differential in the chosen injective resolution to small étale cohomology. -/
def presentation : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
    (positiveShort.{u, w} X Q n).g.hom.ker →+ cohomology.{u, w} X Q (n + 1) :=
  Classical.choose (positive_ext_original_map_naturality.{u, w} X)

/-- Positive cohomology comparison with derived global sections.

For every sheaf and natural `n`, choose the additive equivalence from degree-`n + 1` small
étale cohomology to right-derived global sections determined by resolution representatives. -/
def positiveEquiv : ∀ (Q : CommonSheaf.{u, w} X) (n : ℕ),
    cohomology.{u, w} X Q (n + 1) ≃+ derived.{u, w} X Q (n + 1) :=
  Classical.choose (Classical.choose_spec (positive_ext_original_map_naturality.{u, w} X))

/-- Positive comparison is normalized natural and unique.

The presentation is surjective with kernel the section boundaries; the comparison sends its
values to the corresponding derived cycle classes and respects all closed integral-sheaf
representatives. It is natural in sheaf maps and uniquely determined among comparison families
satisfying these representative conditions. -/
theorem positiveEquiv_spec :
    positiveExtPacket.{u, w} X (presentation.{u, w} X) (positiveEquiv.{u, w} X) ∧
    (∀ (Q Q' : CommonSheaf.{u, w} X) (τ : Q ⟶ Q') (n : ℕ)
      (x : cohomology.{u, w} X Q (n + 1)),
      positiveEquiv.{u, w} X Q' n (Sheaf.H.map τ (n + 1) x) =
        ((gamma.{u, w} X).rightDerived (n + 1)).map τ (positiveEquiv.{u, w} X Q n x)) ∧
    ∀ p e, positiveExtPacket.{u, w} X p e → e = positiveEquiv.{u, w} X :=
  Classical.choose_spec
    (Classical.choose_spec (positive_ext_original_map_naturality.{u, w} X))

/-- Cohomology comparison in every natural degree.

Use the terminal-section comparison in degree zero and the normalized positive comparison in
degree `n + 1` to define `H^q(X,Q) ≃+ R^qΓ(Q)` for every natural `q`. -/
def canonicalEquiv (Q : CommonSheaf.{u, w} X) (q : ℕ) :
    cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q :=
  match q with
  | 0 => zeroEquiv.{u, w} X Q
  | n + 1 => positiveEquiv.{u, w} X Q n

/-- All degree comparison has the positive representative normalization.

In positive degrees, the canonical family has a surjective resolution-cycle presentation with
kernel the boundaries, agrees with derived cycle classes, and represents closed maps from the
integral sheaf by their Ext classes. -/
theorem canonicalEquiv_positive_packet :
    positiveExtPacket.{u, w} X (presentation.{u, w} X)
      (fun Q n => canonicalEquiv.{u, w} X Q (n + 1)) :=
  (positiveEquiv_spec.{u, w} X).1

/-- All degree comparison has the degree zero section normalization.

In degree zero, composing the canonical comparison with the derived-zero and global-section
coordinates gives the terminal-section value of the cohomology class. -/
theorem canonicalEquiv_zero_sections (Q : CommonSheaf.{u, w} X)
    (x : cohomology.{u, w} X Q 0) :
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).hom.app Q
      (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q)
        (canonicalEquiv.{u, w} X Q 0 x)) = smallEtaleH0Sections.{u, w} X Q x :=
  zeroEquiv_sections.{u, w} X Q x

/-- Cohomology comparison is natural in every degree.

For any sheaf map and natural degree `q`, applying its cohomology map and then the target
comparison equals applying the source comparison and then its right-derived global-sections
map. -/
theorem canonicalEquiv_naturality {Q Q' : CommonSheaf.{u, w} X} (τ : Q ⟶ Q')
    (q : ℕ) (x : cohomology.{u, w} X Q q) :
    canonicalEquiv.{u, w} X Q' q (Sheaf.H.map τ q x) =
      ((gamma.{u, w} X).rightDerived q).map τ (canonicalEquiv.{u, w} X Q q x) := by
  cases q with
  | zero => exact zeroEquiv_naturality.{u, w} X τ x
  | succ n => exact (positiveEquiv_spec.{u, w} X).2.1 Q Q' τ n x

/-- Section and representative normalization determine the comparison.

A family of additive cohomology-to-derived equivalences equals the canonical family if it has
the degree-zero terminal-section normalization and a positive resolution-cycle presentation
with the stated boundary and representative normalization. -/
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

/-- Positive comparison evaluates a closed integral sheaf representative.

For a closed map from the integral sheaf to injective-resolution term `n + 1`, its terminal
section is a resolution section cycle, and the comparison sends its Ext representative class
to the derived cycle class of that section. -/
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

/-- Cohomology comparison as an additive group isomorphism.

Bundle the canonical additive equivalence `H^q(X,Q) ≃+ R^qΓ(Q)` as an isomorphism in the
additive-group category. -/
def comparisonIso (Q : CommonSheaf.{u, w} X) (q : ℕ) :
    AddCommGrpCat.of (cohomology.{u, w} X Q q) ≅ derived.{u, w} X Q q :=
  (canonicalEquiv.{u, w} X Q q).toAddCommGrpIso

/-- Group comparison isomorphisms commute with sheaf maps.

The additive-group morphism of the cohomology map followed by the target comparison equals the
source comparison followed by the derived global-sections morphism. -/
@[reassoc]
theorem comparisonIso_naturality {Q Q' : CommonSheaf.{u, w} X} (τ : Q ⟶ Q') (q : ℕ) :
    AddCommGrpCat.ofHom (Sheaf.H.map τ q) ≫ (comparisonIso.{u, w} X Q' q).hom =
      (comparisonIso.{u, w} X Q q).hom ≫ ((gamma.{u, w} X).rightDerived q).map τ := by
  ext x
  exact canonicalEquiv_naturality.{u, w} X τ q x

/-- Inverse cohomology comparison is natural.

The inverse canonical equivalence commutes with the right-derived global-sections map and the
corresponding cohomology map of a sheaf morphism. -/
theorem canonicalEquiv_symm_naturality {Q Q' : CommonSheaf.{u, w} X} (τ : Q ⟶ Q')
    (q : ℕ) (x : derived.{u, w} X Q q) :
    (canonicalEquiv.{u, w} X Q' q).symm (((gamma.{u, w} X).rightDerived q).map τ x) =
      Sheaf.H.map τ q ((canonicalEquiv.{u, w} X Q q).symm x) := by
  apply (canonicalEquiv.{u, w} X Q' q).injective
  rw [AddEquiv.apply_symm_apply, canonicalEquiv_naturality, AddEquiv.apply_symm_apply]

variable {X}
  {S T : ShortComplex (CommonSheaf.{u, w} X)}

/-- Connecting map transported to derived global sections.

For a short exact sheaf sequence, transport its connecting map `H^n(S₃) → H^(n+1)(S₁)` through
the canonical comparisons to obtain an additive map `R^nΓ(S₃) → R^(n+1)Γ(S₁)`. -/
def derivedBoundary (hS : S.ShortExact) (n : ℕ) :
    derived.{u, w} X S.X₃ n →+ derived.{u, w} X S.X₁ (n + 1) :=
  (canonicalEquiv.{u, w} X S.X₁ (n + 1)).toAddMonoidHom.comp
    ((smallEtaleConnectingMap.{u, w} hS n).comp
      (canonicalEquiv.{u, w} X S.X₃ n).symm.toAddMonoidHom)

/-- Transported connecting map respects the cohomology comparison.

The transported boundary applied to the compared source class equals the comparison of its
small étale connecting class. -/
theorem derivedBoundary_comparison (hS : S.ShortExact) (n : ℕ)
    (x : cohomology.{u, w} X S.X₃ n) :
    derivedBoundary.{u, w} hS n (canonicalEquiv.{u, w} X S.X₃ n x) =
      canonicalEquiv.{u, w} X S.X₁ (n + 1) (smallEtaleConnectingMap.{u, w} hS n x) := by
  change canonicalEquiv.{u, w} X S.X₁ (n + 1)
    (smallEtaleConnectingMap.{u, w} hS n
      ((canonicalEquiv.{u, w} X S.X₃ n).symm (canonicalEquiv.{u, w} X S.X₃ n x))) = _
  rw [AddEquiv.symm_apply_apply]

/-- Transported connecting maps are natural in short exact sequences.

For a morphism of short exact sequences, the degree-`n` map on the quotient sheaf commutes
with the transported boundary and the degree-`n + 1` map on the kernel sheaf. -/
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

/-- Six term derived section sequence.

For a short exact sequence, take the three right-derived section objects in degree `n`, the
transported boundary, and the three objects in degree `n + 1`, with the induced first and
second sheaf maps in each degree. -/
def derivedSequence (hS : S.ShortExact) (n : ℕ) :
    ComposableArrows AddCommGrpCat.{max u w} 5 :=
  ComposableArrows.mk₅ (((gamma.{u, w} X).rightDerived n).map S.f)
    (((gamma.{u, w} X).rightDerived n).map S.g)
    (AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n))
    (((gamma.{u, w} X).rightDerived (n + 1)).map S.f)
    (((gamma.{u, w} X).rightDerived (n + 1)).map S.g)

/-- Cohomology and derived section windows are isomorphic.

The six canonical cohomology comparison isomorphisms identify the small étale long-sequence
window with the window of right-derived sections and its transported boundary. -/
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

/-- Derived section windows are exact.

Every six-term derived-section window of a short exact common-universe sheaf sequence is
exact. -/
theorem derivedSequence_exact (hS : S.ShortExact) (n : ℕ) :
    (derivedSequence.{u, w} hS n).Exact :=
  ComposableArrows.exact_of_iso (sequenceComparison.{u, w} hS n)
    (smallEtaleLongSequence_exact.{u, w} hS n)

/-- The first degree zero derived section map is injective.

For a short exact sheaf sequence, the map `R⁰Γ(S.f)` is injective. -/
theorem derivedSequence_initial_injective (hS : S.ShortExact) :
    Function.Injective (((gamma.{u, w} X).rightDerived 0).map S.f) := by
  intro a b hab
  apply (canonicalEquiv.{u, w} X S.X₁ 0).symm.injective
  apply smallEtaleLongSequence_initial_injective hS
  rw [← canonicalEquiv_symm_naturality, ← canonicalEquiv_symm_naturality, hab]

/-- Morphisms of derived section windows.

A morphism of short exact sheaf sequences induces a morphism of their six-term derived-section
windows by the derived maps on its three components in each degree. -/
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

/-- Derived section windows form a functor.

For fixed degree `n`, send short exact sheaf sequences and their morphisms to the six-term
derived-section windows in degrees `n` and `n + 1`. -/
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

/-- Window comparison is natural in short exact sequences.

The cohomology-to-derived section isomorphisms give a natural isomorphism between the two six-
term window functors. -/
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

/-- Six component formulas for a derived window morphism.

The six components are the degree-`n` derived maps of the three sheaf components, followed by
their degree-`n + 1` derived maps, in that order. -/
def DerivedSequenceComponents (X : Scheme.{u}) (n : ℕ)
    {S T : ShortExactSequence (CommonSheaf.{u, w} X)} (α : S ⟶ T) : Prop :=
  let m := (derivedSequenceFunctor.{u, w} X n).map α
  m.app 0 = ((gamma.{u, w} X).rightDerived n).map α.hom.τ₁ ∧
  m.app 1 = ((gamma.{u, w} X).rightDerived n).map α.hom.τ₂ ∧
  m.app 2 = ((gamma.{u, w} X).rightDerived n).map α.hom.τ₃ ∧
  m.app 3 = ((gamma.{u, w} X).rightDerived (n + 1)).map α.hom.τ₁ ∧
  m.app 4 = ((gamma.{u, w} X).rightDerived (n + 1)).map α.hom.τ₂ ∧
  m.app 5 = ((gamma.{u, w} X).rightDerived (n + 1)).map α.hom.τ₃

/-- Derived window functor has the six displayed component maps.

Every morphism image under the derived window functor satisfies the six component formulas for
degrees `n` and `n + 1`. -/
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

/-- Cohomology of sections of an injective resolution.

For an injective resolution of `Q`, apply global sections termwise and take cohomology in
natural degree `q`. -/
abbrev resolutionHomology (X : Scheme.{u}) {Q : CommonSheaf.{u, w} X}
    (R : InjectiveResolution Q) (q : ℕ) :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat.{max u w} (ComplexShape.up ℕ) q).obj
    (((gamma.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ)).obj R.cocomplex)

/-- Connecting map in injective resolution section coordinates.

Conjugate the transported derived-section boundary by the source and target injective-
resolution cohomology isomorphisms to obtain a map from resolution section cohomology in
degree `n` to degree `n + 1`. -/
def resolutionBoundary (hS : S.ShortExact) (n : ℕ)
    (R₁ : InjectiveResolution S.X₁) (R₃ : InjectiveResolution S.X₃) :
    resolutionHomology.{u, w} X R₃ n ⟶ resolutionHomology.{u, w} X R₁ (n + 1) :=
  (R₃.isoRightDerivedObj (gamma.{u, w} X) n).inv ≫
    AddCommGrpCat.ofHom (derivedBoundary.{u, w} hS n) ≫
      (R₁.isoRightDerivedObj (gamma.{u, w} X) (n + 1)).hom

/-- Resolution boundary is independent of the chosen resolutions.

Changing the injective resolutions of the kernel and quotient sheaves through their canonical
cohomology comparisons commutes with the resolution-coordinate connecting map. -/
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

/-- Resolution morphism induces a section cohomology map.

A morphism of injective resolutions over a sheaf map induces the degree-`q` cohomology map
after applying global sections to its cochain map. -/
abbrev resolutionMap {Q Q' : CommonSheaf.{u, w} X} {R : InjectiveResolution Q}
    {R' : InjectiveResolution Q'} {τ : Q ⟶ Q'} (φ : R.Hom R' τ) (q : ℕ) :=
  ((gamma.{u, w} X).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u w} (ComplexShape.up ℕ) q).map φ.hom

/-- Resolution boundaries commute with compatible resolution morphisms.

A morphism of short exact sequences and resolution maps over its first and third sheaf
components give a commutative square with the resolution-coordinate boundaries in degrees `n`
and `n + 1`. -/
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

/-- Lifted coefficient comparisons agree with the canonical family.

A comparison family on coefficient-lifted sheaves agrees in every degree with the canonical
family if it has the degree-zero section normalization and its positive part agrees with a
normalized common-universe resolution presentation. -/
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

/-- Normalized cohomology comparison family.

A family of additive equivalences is normalized if its degree-zero values are terminal
sections and its positive values admit a surjective cycle presentation with boundary kernel
and the integral-sheaf representative condition. -/
def CanonicalFamily (X : Scheme.{u})
    (e : ∀ (Q : CommonSheaf.{u, w} X) (q : ℕ),
      cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q) : Prop :=
  (∀ (Q : CommonSheaf.{u, w} X) (x : cohomology.{u, w} X Q 0),
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{max u w}
      (identityEtaleIsTerminal X)).hom.app Q
      (((gamma.{u, w} X).rightDerivedZeroIsoSelf.hom.app Q) (e Q 0 x)) =
        smallEtaleH0Sections.{u, w} X Q x) ∧
  ∃ p, positiveExtPacket.{u, w} X p (fun Q n => e Q (n + 1))

/-- Normalized cohomology comparison families are unique.

Every normalized comparison family from small étale cohomology to right-derived global
sections equals the canonical family. -/
theorem canonicalFamily_unique (X : Scheme.{u})
    (e : ∀ (Q : CommonSheaf.{u, w} X) (q : ℕ),
      cohomology.{u, w} X Q q ≃+ derived.{u, w} X Q q)
    (h : CanonicalFamily.{u, w} X e) : e = canonicalEquiv.{u, w} X := by
  obtain ⟨p, hp⟩ := h.2
  exact canonicalEquiv_unique.{u, w} X e h.1 p hp

/-- Component naturality and functor laws of derived windows.

These laws state the six component formulas, commutation with every composite arrow of each
window, preservation of identity sequence morphisms, and preservation of their composition. -/
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

/-- Derived window functors satisfy their component and functor laws.

For every natural degree, the derived-window functor has the stated component formulas and
satisfies arrow naturality, identity, and composition laws. -/
theorem derivedFunctorLaws (X : Scheme.{u}) (n : ℕ) : DerivedFunctorLaws.{u, w} X n :=
  ⟨fun _ _ α => derivedSequenceFunctor_components.{u, w} X n α,
    fun _ _ α _ _ h => ((derivedSequenceFunctor.{u, w} X n).map α).naturality (homOfLE h),
    (derivedSequenceFunctor.{u, w} X n).map_id,
    fun _ _ _ α β => (derivedSequenceFunctor.{u, w} X n).map_comp α β⟩

/-- Normalized derived section comparisons and exact sequence laws.

The canonical family has the section and positive-representative normalizations, is natural
and unique, and gives exact six-term windows with an injective first degree-zero map. Its
boundary and window comparisons are natural, while the resolution-coordinate boundaries
commute with changes of resolution and compatible resolution morphisms. -/
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
