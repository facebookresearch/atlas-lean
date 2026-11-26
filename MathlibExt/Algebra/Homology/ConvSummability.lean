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

public import MathlibExt.RingTheory.DifferentialGraded.TwistingCochain
public import MathlibExt.RingTheory.DifferentialGraded.TwistingAugmentationFactor
public import MathlibExt.RingTheory.DifferentialGraded.TensorPowers
public import MathlibExt.RingTheory.DifferentialGraded.CoradicalFiltration
public import MathlibExt.RingTheory.DifferentialGraded.TwistingConilpotentPredicates

/-!
# Convolution vanishing on finite coradical stages

For integer-indexed R-module cochain complexes over a commutative ring,
let C be a comonoid, A a monoid and Δ̄ the reduced comultiplication
relative to η:I → C. A homogeneous cochain f:C → A is reduced when
f∘η=0 and ε∘f=0 for the chosen map ε:A → I.

Filtration stage n consists of homogeneous elements killed by the
(n+1)-st reduced-comultiplication iterate into n+2 tensor factors.
The convolution of two reduced cochains vanishes on stage zero.
If Δ̄=0, the convolution itself is zero.

For a reduced cochain of degree m, with η a comonoid map and ε a monoid
map, the left-accumulating convolution power with n+2 factors has degree
(n+2)m and vanishes on every stage-n element. The statements use the
given graded tensor reassociation/extensionality structures and tensor
preservation of zero objects.
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

/-- Let R be commutative and work with integer-indexed R-module cochain
complexes, with binary graded tensors, coherent threefold and fourfold tensor
reassociation and extensionality, and tensor functors preserving zero.
Let C be a comonoid and A a monoid, with coaugmentation η:I → C,
a map ε:A → I, and reduced comultiplication Δ̄.
Assume Δ_C=Δ̄+(η⊗1)λ_C⁻¹+(1⊗η)ρ_C⁻¹−(η⊗η)λ_I⁻¹ε_C,
η is a comonoid map, and Δ̄ is killed by η and both counit legs.
Let f,g be homogeneous cochains of degrees m,n with
f∘η=g∘η=0 and ε∘f=ε∘g=0.
For x∈C^r in filtration stage zero and s=r+m+n, the component
(f⋆g):C^r → A^s takes x to zero. -/
theorem conv_vanish_of_stageZero {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    (hRed : IsRedComul η Δbar)
    {f : HomComplex.Cochain C A m} {g : HomComplex.Cochain C A n}
    (hf : IsReducedCochain η ε f) (hg : IsReducedCochain η ε g)
    {r s : ℤ} (hrs : r + (m + n) = s) (x : C.X r)
    (hx : IsInFilt Δbar 0 r x) :
    ((conv f g).v r s hrs) x = 0 := by
  have hΔ : (Δbar.f r) x = 0 := by
    have hx0 : ((redComulPowFrom Δbar (0 + 1)).f r) x = 0 := hx
    rw [redComulPowFrom_succ, redComulPowFrom_zero] at hx0
    have hx1 : ((Δbar ≫ HomologicalComplex.tensorHom
      ((HomologicalComplex.leftUnitor C).symm.hom) (𝟙 C)).f r) x = 0 := hx0
    rw [HomologicalComplex.comp_f, ModuleCat.comp_apply] at hx1
    have hIso : HomologicalComplex.tensorHom
          ((HomologicalComplex.leftUnitor C).symm.hom) (𝟙 C) =
        (tensorIsoRight (HomologicalComplex.leftUnitor C).symm).hom := rfl
    rw [hIso] at hx1
    have hE : (tensorIsoRight (C := C) (HomologicalComplex.leftUnitor C).symm).hom ≫
        (tensorIsoRight (C := C) (HomologicalComplex.leftUnitor C).symm).inv = 𝟙 _ :=
      CategoryTheory.Iso.hom_inv_id _
    have hback : (Δbar.f r) x =
        (tensorIsoRight (HomologicalComplex.leftUnitor C).symm).inv.f r
          (((tensorIsoRight (HomologicalComplex.leftUnitor C).symm).hom.f r)
            ((Δbar.f r) x)) := by
      rw [← ModuleCat.comp_apply, ← HomologicalComplex.comp_f, hE,
        HomologicalComplex.id_f, ModuleCat.id_apply]
    rw [hback, hx1]
    exact map_zero _
  rw [conv_eq_redComul_of_reduced hRed hf hg]
  simp only [HomComplex.Cochain.comp_zero_cochain_v,
    HomComplex.Cochain.zero_cochain_comp_v, HomComplex.Cochain.ofHom_v,
    ModuleCat.comp_apply, hΔ, map_zero]

/-- Let R be commutative and work with integer-indexed R-module cochain
complexes, with binary graded tensors, coherent threefold and fourfold tensor
reassociation and extensionality, and tensor functors preserving zero.
Let C be a comonoid and A a monoid, with coaugmentation η:I → C,
a map ε:A → I, and reduced comultiplication Δ̄.
Assume Δ_C=Δ̄+(η⊗1)λ_C⁻¹+(1⊗η)ρ_C⁻¹−(η⊗η)λ_I⁻¹ε_C,
η is a comonoid map, and Δ̄ is killed by η and both counit legs.
If Δ̄=0 and f,g of any integer degrees satisfy
f∘η=g∘η=0 and ε∘f=ε∘g=0, then their convolution f⋆g is zero. -/
theorem conv_eq_zero_of_trivial_redComul {m n : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    (hRed : IsRedComul η Δbar) (hZero : Δbar = 0)
    {f : HomComplex.Cochain C A m} {g : HomComplex.Cochain C A n}
    (hf : IsReducedCochain η ε f) (hg : IsReducedCochain η ε g) :
    conv f g = 0 := by
  rw [conv_eq_redComul_of_reduced hRed hf hg, hZero,
    HomComplex.Cochain.ofHom_zero, HomComplex.Cochain.zero_comp,
    HomComplex.Cochain.zero_comp]

/-- Let R be commutative and work with integer-indexed R-module cochain
complexes, with binary graded tensors, coherent threefold and fourfold tensor
reassociation and extensionality, and tensor functors preserving zero.
Let C be a comonoid and A a monoid, with coaugmentation η:I → C,
a map ε:A → I, and reduced comultiplication Δ̄.
Assume Δ_C=Δ̄+(η⊗1)λ_C⁻¹+(1⊗η)ρ_C⁻¹−(η⊗η)λ_I⁻¹ε_C,
η is a comonoid map, and Δ̄ is killed by η and both counit legs.
Assume the unit comonoid structure is chosen, η is a comonoid morphism
and ε is a monoid morphism. For reduced f of degree m and n∈ℕ,
the left-accumulating convolution power with n+2 factors factors through
the (n+1)-st reduced-comultiplication iterate C → C^{⊗(n+2)} by a
cochain from that tensor power to A of degree (n+2)m. -/
private theorem reducedConvPow_factor_aux {m : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    (hRed : IsRedComul η Δbar)
    {f : HomComplex.Cochain C A m}
    (hf : IsReducedCochain η ε f) (n : ℕ) :
    ∃ G : HomComplex.Cochain (tensorPowObj C (n + 2))
      A ((reducedConvPow f (n + 1)).1),
      (reducedConvPow f (n + 1)).2 =
        (HomComplex.Cochain.ofHom (redComulPowFrom Δbar (n + 1))).comp
          G (zero_add _) := by
  induction n with
  | zero =>
    -- Restate with the computed degree `m + m` (definitionally
    -- `(reducedConvPow f (0 + 1)).1`): this keeps every later degree proof
    -- syntactically uniform, so `rw` motives stay well-typed.
    change ∃ G : HomComplex.Cochain (tensorPowObj C (0 + 2)) A (m + m),
      (reducedConvPow f (0 + 1)).2 =
        (HomComplex.Cochain.ofHom (redComulPowFrom Δbar (0 + 1))).comp
          G (zero_add (m + m))
    refine ⟨(HomComplex.Cochain.ofHom
      (tensorIsoRight (HomologicalComplex.leftUnitor C).symm).inv).comp
      ((HomComplex.Cochain.tensor f f).comp
        (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero (m + m)))
      (zero_add (m + m)), ?_⟩
    have hT : HomologicalComplex.tensorHom
          ((HomologicalComplex.leftUnitor C).symm.hom) (𝟙 C) =
        (tensorIsoRight (HomologicalComplex.leftUnitor C).symm).hom := rfl
    change conv f f =
      (HomComplex.Cochain.ofHom (Δbar ≫ HomologicalComplex.tensorHom
        ((HomologicalComplex.leftUnitor C).symm.hom) (𝟙 C))).comp _ _
    rw [conv_eq_redComul_of_reduced hRed hf hf,
      HomComplex.Cochain.ofHom_comp,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
        (HomComplex.Cochain.ofHom Δbar) _ _ _,
      hT,
      -- Repeated deliberately: each `rw` fires under a single instantiation
      -- only, so each side needs its own association pass.
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
        (HomComplex.Cochain.ofHom Δbar) _ _ _,
      ← HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
        (HomComplex.Cochain.ofHom
          (tensorIsoRight (HomologicalComplex.leftUnitor C).symm).hom) _ _ _,
      ← HomComplex.Cochain.ofHom_comp,
      CategoryTheory.Iso.hom_inv_id,
      HomComplex.Cochain.id_comp]
  | succ n ih =>
    obtain ⟨G, hG⟩ := ih
    have hc : IsReducedCochain η ε (reducedConvPow f (n + 1)).2 :=
      hf.reducedConvPow (n + 1)
    -- Push the `redComulPowFrom` precomposition through the tensor, reusing
    -- `ofHom_tensorHom_comp_tensor`. Eliminating its `(ofHom 𝟙).comp f` leg
    -- by rewriting the composite (not `f` itself, which occurs in iterate
    -- degrees) keeps every motive well-typed.
    have hL := HomComplex.Cochain.ofHom_tensorHom_comp_tensor
      (redComulPowFrom Δbar (n + 1)) (𝟙 C) G f
    rw [HomComplex.Cochain.id_comp f] at hL
    -- Restate with the computed degree `(reducedConvPow f (n + 1)).1 + m`
    -- (definitionally `(reducedConvPow f (n + 1 + 1)).1`): this keeps every
    -- later degree proof syntactically uniform, so `rw` motives stay
    -- well-typed.
    change ∃ G : HomComplex.Cochain (tensorPowObj C (n + 1 + 2))
        A ((reducedConvPow f (n + 1)).1 + m),
      (reducedConvPow f (n + 1 + 1)).2 =
        (HomComplex.Cochain.ofHom (redComulPowFrom Δbar (n + 1 + 1))).comp
          G (zero_add ((reducedConvPow f (n + 1)).1 + m))
    refine ⟨(HomComplex.Cochain.tensor G f).comp
      (HomComplex.Cochain.ofHom (MonObj.mul (X := A))) (add_zero _), ?_⟩
    change conv (reducedConvPow f (n + 1)).2 f =
      (HomComplex.Cochain.ofHom (Δbar ≫ HomologicalComplex.tensorHom
        (redComulPowFrom Δbar (n + 1)) (𝟙 C))).comp _ _
    rw [conv_eq_redComul_of_reduced hRed hc hf, hG, hL.symm,
      HomComplex.Cochain.ofHom_comp,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
        (HomComplex.Cochain.ofHom Δbar) _ _ _,
      -- Repeated deliberately: each `rw` fires under a single instantiation
      -- only, so each side needs its own association pass.
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
        (HomComplex.Cochain.ofHom Δbar) _ _ _,
      HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain
        (HomComplex.Cochain.ofHom (HomologicalComplex.tensorHom
          (redComulPowFrom Δbar (n + 1)) (𝟙 C))) _ _ _]

/-- Let R be commutative and work with integer-indexed R-module cochain
complexes, with binary graded tensors, coherent threefold and fourfold tensor
reassociation and extensionality, and tensor functors preserving zero.
Let C be a comonoid and A a monoid, with coaugmentation η:I → C,
a map ε:A → I, and reduced comultiplication Δ̄.
Assume Δ_C=Δ̄+(η⊗1)λ_C⁻¹+(1⊗η)ρ_C⁻¹−(η⊗η)λ_I⁻¹ε_C,
η is a comonoid map, and Δ̄ is killed by η and both counit legs.
Assume the unit comonoid structure is chosen, η is a comonoid morphism
and ε is a monoid morphism. For reduced f of degree m, n∈ℕ and
x∈C^r killed by the (n+1)-st reduced-comultiplication iterate,
the n+2-factor left-accumulating convolution power of f takes x to
zero in degree r+(n+2)m. -/
theorem reducedConvPow_vanish_of_mem {m : ℤ}
    {η : 𝟙_ (CochainComplex (ModuleCat R) ℤ) ⟶ C}
    {ε : A ⟶ 𝟙_ (CochainComplex (ModuleCat R) ℤ)}
    {Δbar : C ⟶ HomologicalComplex.tensorObj C C}
    [ComonObj (𝟙_ (CochainComplex (ModuleCat R) ℤ))]
    [IsComonHom η] [IsMonHom ε]
    (hRed : IsRedComul η Δbar)
    {f : HomComplex.Cochain C A m}
    (hf : IsReducedCochain η ε f) (n : ℕ)
    {r s : ℤ} (hrs : r + (reducedConvPow f (n + 1)).1 = s) (x : C.X r)
    (hx : IsInFilt Δbar n r x) :
    (((reducedConvPow f (n + 1)).2.v r s hrs) x) = 0 := by
  obtain ⟨G, hG⟩ := reducedConvPow_factor_aux hRed hf n
  rw [hG]
  have hx0 : ((redComulPowFrom Δbar (n + 1)).f r) x = 0 := hx
  simp only [HomComplex.Cochain.zero_cochain_comp_v,
    HomComplex.Cochain.ofHom_v, ModuleCat.comp_apply, hx0, map_zero]

end CochainComplex
