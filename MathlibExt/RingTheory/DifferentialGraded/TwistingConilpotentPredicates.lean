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
# Finite convolution nilpotence of homogeneous cochains

For a degree-m cochain f from a cochain comonoid C to a monoid A, define the degree/cochain
pair P₀=(m,f) and Pₙ₊₁=(dₙ+m,fₙ⋆f) when Pₙ=(dₙ,fₙ). Thus the iteration starts at f and has n+1
factors, accumulated on the left. Finite convolution nilpotence means fₙ=0 as a whole
homogeneous cochain for some n.

These degree-recorded iterates commute with monoid postcomposition and comonoid
precomposition, and nilpotence is preserved by both. For compatible augmentation maps,
reducedness of f implies reducedness of every iterate at its recorded degree.

If IsRedComul η b holds, reduced f,g satisfy f⋆g = μ_A∘(f⊗g)∘b. In particular, b=0 makes f⋆f
zero for every reduced f and hence gives finite convolution nilpotence. This applies to the
underlying cochain of a twisting cochain. The setting retains all integer degrees and the
stated cochain tensor hypotheses.
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

/-- Finite convolution iterates with their homogeneous degrees.

For f of degree m, define P₀=(m,f). If Pₙ=(dₙ,fₙ), define Pₙ₊₁=(dₙ+m,fₙ⋆f). Each value is a
pair of an integer degree and a cochain in that degree. -/
noncomputable def reducedConvPow {m : ℤ} (f : HomComplex.Cochain C A m) :
    ℕ → Σ d : ℤ, HomComplex.Cochain C A d
  | 0 => ⟨m, f⟩
  | n + 1 => ⟨(reducedConvPow f n).1 + m, conv (reducedConvPow f n).2 f⟩

/-- Initial degree-recorded convolution iterate.

For a degree-m cochain f, reducedConvPow f 0 is the pair (m,f). -/
@[simp] theorem reducedConvPow_zero {m : ℤ} (f : HomComplex.Cochain C A m) :
    reducedConvPow f 0 = ⟨m, f⟩ :=
  rfl

/-- Successor degree-recorded convolution iterate.

If reducedConvPow f n is (dₙ,fₙ), its successor is (dₙ+m,fₙ⋆f), with f of degree m on the
right. -/
@[simp] theorem reducedConvPow_succ {m : ℤ} (f : HomComplex.Cochain C A m) (n : ℕ) :
    reducedConvPow f (n + 1) =
      ⟨(reducedConvPow f n).1 + m, conv (reducedConvPow f n).2 f⟩ :=
  rfl

/-- Reduction preserved by finite convolution iteration.

Assume a comonoid structure on I, η : I → C a comonoid morphism and ε : A → I a monoid
morphism. If f is reduced for η,ε, then every cochain component of reducedConvPow f n is
reduced at its recorded integer degree. -/
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

/-- Monoid postcomposition of degree-recorded convolution iterates.

For a monoid morphism φ : A → B, iterating f followed by φ gives the same recorded degree as
iterating f, and its cochain component is fₙ followed by φ. No reduction or vanishing
hypothesis on f is used. -/
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

/-- Comonoid precomposition of degree-recorded convolution iterates.

For a comonoid morphism ψ : C' → C, iterating ψ followed by f gives the recorded degree dₙ and
cochain ψ followed by fₙ, where (dₙ,fₙ)=reducedConvPow f n. -/
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

/-- Vanishing of a finite convolution iterate.

For any homogeneous f, IsReducedConvNilpotent f means that some cochain component fₙ of
reducedConvPow f n equals zero. This is a single finite witness for the whole cochain, and the
predicate itself does not require augmentation reducedness. -/
def IsReducedConvNilpotent {m : ℤ} (f : HomComplex.Cochain C A m) : Prop :=
  ∃ n : ℕ, (reducedConvPow f n).2 = 0

/-- Finite convolution nilpotence of a twisting cochain.

A twisting cochain τ satisfies this predicate when its underlying degree-one cochain τ.tau has
a vanishing finite convolution iterate. -/
def TwistingCochain.IsReducedConvNilpotent
    (τ : TwistingCochain (R := R) (C := C) (A := A)) : Prop :=
  CochainComplex.IsReducedConvNilpotent τ.tau

/-- Finite convolution nilpotence of the zero cochain.

The zero cochain in any integer degree is convolution nilpotent: its iterate at n=1 is 0⋆0=0. -/
theorem IsReducedConvNilpotent.zero {m : ℤ} :
    IsReducedConvNilpotent (0 : HomComplex.Cochain C A m) :=
  ⟨1, conv_zero_left _⟩

/-- Convolution nilpotence preserved by a monoid morphism.

If a homogeneous f has a vanishing finite convolution iterate and φ : A → B is a monoid
morphism, then f followed by φ has a vanishing iterate at the same index. -/
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

/-- Convolution nilpotence preserved by a comonoid morphism.

If f has a vanishing finite convolution iterate and ψ : C' → C is a comonoid morphism, then ψ
followed by f has a vanishing iterate at the same index. -/
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

/-- Convolution of reduced factors through a reduced coproduct.

For IsRedComul η b and homogeneous f,g reduced with respect to η,ε, f⋆g equals the degree-zero
map b followed by their tensor cochain and μ_A. All coaugmentation terms in Δ_C vanish on the
reduced factors. -/
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

/-- Convolution nilpotence from a zero reduced coproduct.

If IsRedComul η b holds, b=0 and f is reduced for η,ε, then f⋆f=0. Consequently reducedConvPow
f 1 vanishes and f is finite convolution nilpotent. -/
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

/-- Twisting-cochain nilpotence from a zero reduced coproduct.

For a twisting cochain τ, if IsRedComul τ.coaug b holds and b=0, then
τ.IsReducedConvNilpotent. Its underlying cochain is reduced by the twisting fields, so its
two-factor convolution vanishes. -/
theorem TwistingCochain.isReducedConvNilpotent_of_trivial_redComul
    (τ : TwistingCochain (R := R) (C := C) (A := A))
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    (hRed : IsRedComul τ.coaug Δbar) (hZero : Δbar = 0) :
    τ.IsReducedConvNilpotent :=
  IsReducedConvNilpotent.of_trivial_redComul hRed hZero τ.reduced

end CochainComplex
