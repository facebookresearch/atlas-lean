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

public import MathlibExt.RingTheory.DifferentialGraded.CoradicalFiltration
public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor
public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain

/-!
# Reduced convolution-nilpotence as the conilpotence-side prerequisite

This file packages finite reduced convolution-nilpotence of homogeneous
cochains, the conilpotence-side prerequisite for twisting morphisms. It uses
only the accepted `TwistingCochain`, `conv`, `Cochain.ofHom` /
`Cochain.comp`, `TwistingAugmentationFactor` (`IsReducedCochain`,
`conv_of_left`), `CoradicalFiltration` (`IsRedComul`), and the existing
`(co)monoid` APIs.

For `f : HomComplex.Cochain C A m`, `reducedConvPow f n` iterates the graded
convolution `conv` (`f ⋆ g = μ ∘ (f ⊗ g) ∘ Δ`, assembled from
`ComonObj.comul`, `tensorCochain`, and `MonObj.mul` via `Cochain.comp`).
`IsReducedConvNilpotent f` holds when some reduced iterate vanishes. Every
twisting cochain carries its underlying degree-`+1` cochain, so
`TwistingCochain.IsReducedConvNilpotent` is the twisting-level wrapper. The
zero cochain is nilpotent (`IsReducedConvNilpotent.zero`, via the accepted
`conv_zero_left`).

Reduced iterates are base-at-`f` and left-accumulating: `pow 0 = f` and
`pow (n+1) = conv (pow n) f`. They are distinct from a unital monoid power
(the degree-`0` unit `convOne` is non-reduced, so a unital tower belongs to a
later convolution-monoid power API, not here), from `IsReducedCochain`
(augmentation/coaugmentation vanishing, not iterate vanishing), from
coalgebra-domain conilpotence (a coalgebra-side coradical condition, not a
cochain iterate condition), and from adic completeness (augmentation-ideal
powers, quotient tower, adic completion/comparison, and nilpotent completeness
live in `AugIdealPowers`, `AugIdealQuotientTower`, `AugIdealAdicCompletion`,
`AugIdealAdicComparison`, and `AugIdealNilpotentComplete`, not here).

Primary source: no external source beyond pinned Mathlib and the explicit
`TwistingCochain` API is used here; no match to a printed Loday–Vallette
section or sign convention is claimed.

## Declaration inventory

* `reducedConvPow`: reduced iterated convolution powers as a degree-hiding
  sigma (`0 ↦ f`, `n+1 ↦ conv (pow n) f`).
* `IsReducedConvNilpotent`: finite reduced convolution-nilpotence
  (`∃ n, pow n = 0`).
* `TwistingCochain.IsReducedConvNilpotent`: wrapper for `τ.tau`.
* `IsReducedConvNilpotent.zero`: the zero cochain is nilpotent.
* `reducedConvPow_zero` / `reducedConvPow_succ`: unfolding lemmas.
* `IsReducedCochain.reducedConvPow`: every sigma-valued reduced iterate of a
  reduced cochain is reduced at its actual hidden degree, by induction through
  `IsReducedCochain.conv_of_left`. Preservation only; not nilpotence/support.
* `conv_eq_redComul_of_reduced`: one-step compatibility between full
  convolution and reduced-bar convolution via the `IsRedComul` decomposition:
  for reduced factors, `conv f g` equals `μ ∘ (f ⊗ g) ∘ Δbar`.
* `IsReducedConvNilpotent.of_trivial_redComul`: uniform stage-0 bridge: when
  the reduced comultiplication itself vanishes (`Δbar = 0`), every reduced
  cochain is convolution-nilpotent in one step.
* `TwistingCochain.isReducedConvNilpotent_of_trivial_redComul`: twisting-level
  wrapper, via `TwistingCochain.reduced`.

## Completeness lives elsewhere; comparison is deferred here

Augmentation-ideal powers, quotient tower, adic completion, adic comparison,
and nilpotent completeness are supplied by `AugIdealPowers`,
`AugIdealQuotientTower`, `AugIdealAdicCompletion`, `AugIdealAdicComparison`,
and `AugIdealNilpotentComplete`, not by this leaf. This leaf proves no
completeness. Deferred here are only the convolution-nilpotence versus
adic-completeness comparison and coideal-side completeness; no ideal/coideal
monoid/comonoid structure is claimed. In particular, completeness is not
encoded as nilpotence and not encoded as a retraction.

## Nonclaims

* No free/cofree (co)algebra objects, no universal-property fields, no
  representability equivalence, no adjunction, no totalization, and no
  derived/Koszul claim.
* No `conv_assoc`, `conv_one_left` / `conv_one_right`: those are proved in
  `TwistingConvolutionMonoid`, not here.
* No conilpotence/completeness equivalence: that needs the deferred
  infrastructure above.
* Reducedness preservation along `reducedConvPow` is not nilpotence and not
  support: it states every iterate is reduced, never that an iterate vanishes
  or that convolution support is finite.
* The bridge above is uniform stage-0 only (`Δbar = 0` as a morphism).
  Pointwise `IsConilpotent` exhaustion alone does not imply a uniform bound,
  so it does not imply `IsReducedConvNilpotent` without a finiteness hypothesis;
  higher uniform stages need iterated multiplication and tensor-power coherence
  that are absent here, and are deferred rather than stubbed.
* No homological (`down ℤ`) API; everything is cohomological.

## Import justification

`TwistingCochain` supplies `conv`, the zero laws `conv_zero_left` and
`conv_zero_right`, `tensorCochain_eq_tensor`, and the `TwistingCochain`
structure. `TwistingAugmentationFactor` supplies `IsReducedCochain` and
`IsReducedCochain.conv_of_left`. `CoradicalFiltration` supplies `IsRedComul`
(and hence the honest comultiplication decomposition); it imports only
`TwistingAugmentationFactor`, `TensorPowers`, and `ReducedKernels`, so this
import is acyclic.
All three direct imports are used below.
-/

@[expose] public section

open CategoryTheory Limits MonoidalCategory

namespace CochainComplex

variable {R : Type*} [CommRing R]
variable {C A : CochainComplex (ModuleCat R) ℤ}

variable [∀ (X₁ X₂ : GradedObject ℤ (ModuleCat R)), GradedObject.HasTensor X₁ X₂]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).obj X)]
variable [∀ (X : ModuleCat R), PreservesColimit (Functor.empty.{0} (ModuleCat R))
  ((curriedTensor (ModuleCat R)).flip.obj X)]
variable [∀ (X₁ X₂ X₃ X₄ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
variable [∀ (X₁ X₂ X₃ : GradedObject ℤ (ModuleCat R)),
  GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

variable [MonObj A] [ComonObj C]

/-- Reduced iterated convolution powers of a homogeneous cochain, with the
degree hidden in a sigma: `0 ↦ f` and `n+1 ↦ conv (pow n) f`.
Base-at-`f`, left-accumulating; not a unital monoid power. -/
noncomputable def reducedConvPow {m : ℤ} (f : HomComplex.Cochain C A m) :
    ℕ → Σ d : ℤ, HomComplex.Cochain C A d
  | 0 => ⟨m, f⟩
  | n + 1 => ⟨(reducedConvPow f n).1 + m, conv (reducedConvPow f n).2 f⟩

@[simp] theorem reducedConvPow_zero {m : ℤ} (f : HomComplex.Cochain C A m) :
    reducedConvPow f 0 = ⟨m, f⟩ :=
  rfl

@[simp] theorem reducedConvPow_succ {m : ℤ} (f : HomComplex.Cochain C A m) (n : ℕ) :
    reducedConvPow f (n + 1) =
      ⟨(reducedConvPow f n).1 + m, conv (reducedConvPow f n).2 f⟩ :=
  rfl

/-- Every sigma-valued reduced-convolution iterate of a reduced cochain is
reduced at its actual hidden degree, by induction consuming the induction
hypothesis through `IsReducedCochain.conv_of_left` with arbitrary right
factor `f`. Preservation only; not nilpotence and not support. -/
theorem IsReducedCochain.reducedConvPow {m : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    {f : HomComplex.Cochain C A m}
    (hf : IsReducedCochain η ε f) (n : ℕ) :
    IsReducedCochain η ε (reducedConvPow f n).2 := by
  induction n with
  | zero => simpa [reducedConvPow_zero] using hf
  | succ n ih =>
    rw [reducedConvPow_succ]
    exact IsReducedCochain.conv_of_left _ ih

/-- Reduced iterates commute with target postcomposition by a monoid morphism,
by induction consuming `conv_postcomp` at the successor step. No vanishing,
reducedness, or augmentation hypothesis is needed for the transport itself. -/
theorem reducedConvPow_postcomp {B : CochainComplex (ModuleCat R) ℤ} [MonObj B]
    {m : ℤ} (f : HomComplex.Cochain C A m) (φ : A ⟶ B) [IsMonHom φ] (n : ℕ) :
    reducedConvPow (f.comp (HomComplex.Cochain.ofHom φ) (add_zero m)) n =
      ⟨(reducedConvPow f n).1,
        (reducedConvPow f n).2.comp (HomComplex.Cochain.ofHom φ)
          (add_zero (reducedConvPow f n).1)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reducedConvPow_succ, reducedConvPow_succ, ih]
    simp only [conv_postcomp]

/-- Reduced iterates commute with source precomposition by a comonoid morphism,
by induction consuming `conv_precomp` at the successor step. No vanishing,
reducedness, or coaugmentation hypothesis is needed for the transport itself. -/
theorem reducedConvPow_precomp {C' : CochainComplex (ModuleCat R) ℤ} [ComonObj C']
    {m : ℤ} (f : HomComplex.Cochain C A m) (ψ : C' ⟶ C) [IsComonHom ψ] (n : ℕ) :
    reducedConvPow ((HomComplex.Cochain.ofHom ψ).comp f (zero_add m)) n =
      ⟨(reducedConvPow f n).1,
        (HomComplex.Cochain.ofHom ψ).comp (reducedConvPow f n).2
          (zero_add (reducedConvPow f n).1)⟩ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [reducedConvPow_succ, reducedConvPow_succ, ih]
    simp only [conv_precomp]

/-- Finite reduced convolution-nilpotence of a homogeneous cochain: some
reduced iterate vanishes. This is the sound conilpotence-side prerequisite;
comparison with adic completeness is explicitly deferred (see the module documentation). -/
def IsReducedConvNilpotent {m : ℤ} (f : HomComplex.Cochain C A m) : Prop :=
  ∃ n : ℕ, (reducedConvPow f n).2 = 0

/-- A twisting cochain is reduced convolution-nilpotent when its underlying
degree-`+1` cochain is. -/
def TwistingCochain.IsReducedConvNilpotent
    (τ : TwistingCochain (R := R) (C := C) (A := A)) : Prop :=
  CochainComplex.IsReducedConvNilpotent τ.tau

/-- The zero cochain is reduced convolution-nilpotent in one step, via the
accepted `conv_zero_left`. -/
theorem IsReducedConvNilpotent.zero {m : ℤ} :
    IsReducedConvNilpotent (0 : HomComplex.Cochain C A m) :=
  ⟨1, conv_zero_left _⟩

/-- Reduced convolution-nilpotence is preserved by target postcomposition with a
monoid morphism, by transporting the vanishing witness through
`reducedConvPow_postcomp` and `Cochain.zero_comp`. -/
theorem IsReducedConvNilpotent.postcomp {B : CochainComplex (ModuleCat R) ℤ}
    [MonObj B] {m : ℤ} {f : HomComplex.Cochain C A m}
    (hf : IsReducedConvNilpotent f) (φ : A ⟶ B) [IsMonHom φ] :
    IsReducedConvNilpotent
      (f.comp (HomComplex.Cochain.ofHom φ) (add_zero m)) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have hPow := reducedConvPow_postcomp f φ n
  rw [hPow]
  simp only [hn, HomComplex.Cochain.zero_comp]

/-- Reduced convolution-nilpotence is preserved by source precomposition with a
comonoid morphism, by transporting the vanishing witness through
`reducedConvPow_precomp` and `Cochain.comp_zero`. -/
theorem IsReducedConvNilpotent.precomp {C' : CochainComplex (ModuleCat R) ℤ}
    [ComonObj C'] {m : ℤ} {f : HomComplex.Cochain C A m}
    (hf : IsReducedConvNilpotent f) (ψ : C' ⟶ C) [IsComonHom ψ] :
    IsReducedConvNilpotent
      ((HomComplex.Cochain.ofHom ψ).comp f (zero_add m)) := by
  obtain ⟨n, hn⟩ := hf
  refine ⟨n, ?_⟩
  have hPow := reducedConvPow_precomp f ψ n
  rw [hPow]
  simp only [hn, HomComplex.Cochain.comp_zero]

-- The section tensor/monoid/comonoid instances are genuinely unused here: the
-- statement is over arbitrary source complexes. The left-zero law is supplied
-- by `HomComplex.Cochain.tensor_zero_left`; only the right-sided analogue
-- remains local.
set_option linter.unusedSectionVars false in
/-- Heterogeneous tensor product vanishes when the right factor vanishes.
Proof mirrors `tensorCochain_zero_right`; stated over arbitrary source
complexes since the `η`-legs land in `𝟙_`; kept private since its consumer
lives in this file. -/
private theorem het_tensor_zero_right
    {C₁ C₂ A₁ A₂ : CochainComplex (ModuleCat R) ℤ} {m n : ℤ}
    (f : HomComplex.Cochain C₁ A₁ m) :
    HomComplex.Cochain.tensor f (0 : HomComplex.Cochain C₂ A₂ n) = 0 := by
  apply HomComplex.Cochain.ext
  intro r s hrs
  rw [HomComplex.Cochain.tensor_v, HomComplex.Cochain.zero_v]
  apply HomologicalComplex.mapBifunctor.hom_ext (c := ComplexShape.up ℤ)
  intro i₁ i₂ hh
  rw [HomologicalComplex.ι_mapBifunctorDesc]
  simp only [HomComplex.Cochain.zero_v,
    MonoidalPreadditive.tensor_zero, smul_zero, zero_comp, comp_zero]

/-- One-step compatibility between full convolution and reduced-bar
convolution: for reduced factors, `conv f g` equals `μ ∘ (f ⊗ g) ∘ Δbar`,
using the `IsRedComul` decomposition with correctly oriented tensor maps.
Each `η`-leg vanishes because the reduced factors kill the coaugmentation;
only the augmentation-side statement is unused. -/
theorem conv_eq_redComul_of_reduced {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    (hRed : IsRedComul η Δbar)
    {f : HomComplex.Cochain C A m} {g : HomComplex.Cochain C A n}
    (hf : IsReducedCochain η ε f) (hg : IsReducedCochain η ε g) :
    conv f g =
      (((HomComplex.Cochain.ofHom Δbar).comp
        (HomComplex.Cochain.tensor f g) (zero_add (m + n))).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero (m + n))) := by
  obtain ⟨_, hΔ, _, _, _⟩ := hRed
  have hL : ((HomComplex.Cochain.ofHom
      ((HomologicalComplex.leftUnitor C).inv ≫
        HomologicalComplex.tensorHom η (𝟙 C))).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))) = 0 := by
    rw [HomComplex.Cochain.ofHom_comp,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.ofHom_tensorHom_comp_tensor,
      hf.1, HomComplex.Cochain.tensor_zero_left,
      HomComplex.Cochain.comp_zero]
  have hR : ((HomComplex.Cochain.ofHom
      ((HomologicalComplex.rightUnitor C).inv ≫
        HomologicalComplex.tensorHom (𝟙 C) η)).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))) = 0 := by
    rw [HomComplex.Cochain.ofHom_comp,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.ofHom_tensorHom_comp_tensor,
      hg.1, het_tensor_zero_right,
      HomComplex.Cochain.comp_zero]
  have hU : ((HomComplex.Cochain.ofHom
      (ComonObj.counit (X := C) ≫
        (HomologicalComplex.leftUnitor _).inv ≫
        HomologicalComplex.tensorHom η η)).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))) = 0 := by
    rw [← Category.assoc, HomComplex.Cochain.ofHom_comp,
      HomComplex.Cochain.ofHom_comp,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain,
      HomComplex.Cochain.ofHom_tensorHom_comp_tensor,
      hf.1, HomComplex.Cochain.tensor_zero_left,
      HomComplex.Cochain.comp_zero, HomComplex.Cochain.comp_zero]
  have hMain : ((HomComplex.Cochain.ofHom (ComonObj.comul (X := C))).comp
      (HomComplex.Cochain.tensor f g) (zero_add (m + n))) =
      (HomComplex.Cochain.ofHom Δbar).comp
        (HomComplex.Cochain.tensor f g) (zero_add (m + n)) := by
    rw [hΔ, HomComplex.Cochain.ofHom_sub, HomComplex.Cochain.ofHom_add,
      HomComplex.Cochain.ofHom_add, HomComplex.Cochain.sub_comp,
      HomComplex.Cochain.add_comp, HomComplex.Cochain.add_comp,
      hL, hR, hU, add_zero, add_zero, sub_zero]
  unfold conv
  rw [tensorCochain_eq_tensor, hMain]

/-- Uniform stage-0 conilpotence-to-convolution bridge: when the reduced
comultiplication itself vanishes, every reduced cochain is convolution
nilpotent in one step. This is the strongest implication the public
API supports; higher uniform stages need absent iterated multiplication. -/
theorem IsReducedConvNilpotent.of_trivial_redComul {m : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    (hRed : IsRedComul η Δbar) (hZero : Δbar = 0)
    {f : HomComplex.Cochain C A m}
    (hf : IsReducedCochain η ε f) :
    IsReducedConvNilpotent f := by
  refine ⟨1, ?_⟩
  rw [show (1 : ℕ) = 0 + 1 from rfl, reducedConvPow_succ, reducedConvPow_zero]
  change conv f f = 0
  rw [conv_eq_redComul_of_reduced hRed hf hf, hZero,
    HomComplex.Cochain.ofHom_zero, HomComplex.Cochain.zero_comp,
    HomComplex.Cochain.zero_comp]

/-- Twisting-level wrapper: a twisting cochain over a trivial reduced
comultiplication is reduced convolution-nilpotent. -/
theorem TwistingCochain.isReducedConvNilpotent_of_trivial_redComul
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    (hRed : IsRedComul τ.coaug Δbar) (hZero : Δbar = 0) :
    τ.IsReducedConvNilpotent :=
  IsReducedConvNilpotent.of_trivial_redComul hRed hZero τ.reduced

end CochainComplex
