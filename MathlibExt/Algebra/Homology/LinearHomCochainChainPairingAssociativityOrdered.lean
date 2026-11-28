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

public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairingAssociativity

/-!
# Ordered mixed cup–cap associativity

Let R be commutative and all coefficient modules lie in universe u. The ordered mixed identity
compares (a∪b)⌢_l z with b⌢₂(a⌢₁u(z)). For cochain degrees p,q and output chain degree r, its
input degrees are (p+q)+r and p+(q+r). The ordinary module braiding exchanges the two cochain
factors before the associator; no degree-dependent braiding multiplier is inserted into this
identity.

Compatible input and output maps on terms, cycles and homology carry a termwise ordered identity
to homology. For linear Hom cochains, the required termwise identity follows from a specified
diagram of the cup diagonal, two ordered cap diagonals and their coefficient actions. The
comparison maps and their full degree transports remain part of the statements.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace HomologicalComplex.CochainChainGradedPairing

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u. Let
P₁₂:K₁,K₂→K₁₂ be a cochain graded product and P_l:K₁₂,L→M_l, P₁:K₁,L→M₁, P₂:K₂,M₁→M_r mixed
pairings. For p,q,r put n=(p+q)+r, n′=p+(q+r), and choose u_Z:Z_nL→Z_{n′}L, u_H:H_nL→H_{n′}L
with π_n≫u_H=u_Z≫π_{n′}, and c:H_rM_l→H_rM_r. If c([P_l^Z(P₁₂^Z(x,y),z)])=[P₂^Z(y,P₁^Z(x,u_Zz))]
on cycles, then c((a∪b)⌢_l t)=b⌢₂(a⌢₁u_H(t)) on homology. The tensor-map expression uses
ordinary braiding of the cochain factors and the associator. -/
private theorem pairHomology_associativity_ordered
    {K₁ K₂ K₁₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M₁ Mₗ Mᵣ : ChainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainChainGradedPairing K₁₂ L Mₗ)
    (P₁ : CochainChainGradedPairing K₁ L M₁)
    (P₂ : CochainChainGradedPairing K₂ M₁ Mᵣ)
    (p q r : ℕ)
    (inputCycles : L.cycles ((p + q) + r) ⟶ L.cycles (p + (q + r)))
    (input : L.homology ((p + q) + r) ⟶ L.homology (p + (q + r)))
    (comparison : Mₗ.homology r ⟶ Mᵣ.homology r)
    (input_π : L.homologyπ ((p + q) + r) ≫ input =
      inputCycles ≫ L.homologyπ (p + (q + r)))
    (hcycles :
      (P₁₂.pairCycles p q ⊗ₘ 𝟙 (L.cycles ((p + q) + r))) ≫
          Pₗ.pairCycles (p + q) r ≫ Mₗ.homologyπ r ≫ comparison =
        ((β_ (K₁.cycles p) (K₂.cycles q)).hom ⊗ₘ
            𝟙 (L.cycles ((p + q) + r))) ≫
          (α_ (K₂.cycles q) (K₁.cycles p)
            (L.cycles ((p + q) + r))).hom ≫
          (𝟙 (K₂.cycles q) ⊗ₘ
            ((𝟙 (K₁.cycles p) ⊗ₘ inputCycles) ≫
              P₁.pairCycles p (q + r))) ≫
          P₂.pairCycles q r ≫ Mᵣ.homologyπ r) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (L.homology ((p + q) + r))) ≫
        Pₗ.pairHomology (p + q) r ≫ comparison =
      ((β_ (K₁.homology p) (K₂.homology q)).hom ⊗ₘ
          𝟙 (L.homology ((p + q) + r))) ≫
        (α_ (K₂.homology q) (K₁.homology p)
          (L.homology ((p + q) + r))).hom ≫
        (𝟙 (K₂.homology q) ⊗ₘ
          ((𝟙 (K₁.homology p) ⊗ₘ input) ≫
            P₁.pairHomology p (q + r))) ≫
        P₂.pairHomology q r := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro x y z
  obtain ⟨x₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₁.homologyπ p)).mp inferInstance x
  obtain ⟨y₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective (K₂.homologyπ q)).mp inferInstance y
  obtain ⟨z₀, rfl⟩ :=
    (ModuleCat.epi_iff_surjective
      (L.homologyπ ((p + q) + r))).mp inferInstance z
  change comparison.hom
      ((Pₗ.pairHomology (p + q) r).hom
        ((P₁₂.pairHomology p q).hom
            ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
              (K₂.homologyπ q).hom y₀) ⊗ₜ[R]
          (L.homologyπ ((p + q) + r)).hom z₀)) =
    (P₂.pairHomology q r).hom
      ((K₂.homologyπ q).hom y₀ ⊗ₜ[R]
        (P₁.pairHomology p (q + r)).hom
          ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
            input.hom ((L.homologyπ ((p + q) + r)).hom z₀)))
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply R P₁₂,
    pairHomology_π_apply R Pₗ]
  have hinput := ConcreteCategory.congr_hom input_π z₀
  change input.hom ((L.homologyπ ((p + q) + r)).hom z₀) =
    (L.homologyπ (p + (q + r))).hom (inputCycles.hom z₀) at hinput
  rw [hinput, pairHomology_π_apply R P₁, pairHomology_π_apply R P₂]
  exact ConcreteCategory.congr_hom hcycles
    ((x₀ ⊗ₜ[R] y₀) ⊗ₜ[R] z₀)

/-- Let R be commutative in universe u. Let K₁,K₂,K₁₂ be nonnegative cochain complexes and
L,M₁,M_l,M_r nonnegative chain complexes of R-modules with carriers in u. Let P₁₂ pair K₁,K₂
into K₁₂, and let P_l:K₁₂,L→M_l, P₁:K₁,L→M₁ and P₂:K₂,M₁→M_r be mixed graded pairings. For
p,q,r∈ℕ put n=(p+q)+r and n′=p+(q+r).

Choose maps u_X:L_n→L_{n′}, u_Z:Z_nL→Z_{n′}L, u_H:H_nL→H_{n′}L and c_X:(M_l)_r→(M_r)_r,
c_Z:Z_rM_l→Z_rM_r, c_H:H_rM_l→H_rM_r. Assume u_Z≫i_{L,n′}=i_{L,n}≫u_X, π_{L,n}≫u_H=u_Z≫π_{L,n′},
c_Z≫i_{M_r,r}=i_{M_l,r}≫c_X and π_{M_l,r}≫c_H=c_Z≫π_{M_r,r}.

If c_X(P_l(P₁₂(x,y),z))=P₂(y,P₁(x,u_Xz)) on terms of degrees p,q,n, with the ordinary module
braiding exchanging x,y before reassociation, then c_H((a∪_{12}b)⌢_l t)=b⌢₂(a⌢₁u_H(t)) on
classes. The conclusion uses that same ordinary braiding and associator. -/
public theorem pairHomology_associativity_ordered_of_pair
    {K₁ K₂ K₁₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M₁ Mₗ Mᵣ : ChainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainChainGradedPairing K₁₂ L Mₗ)
    (P₁ : CochainChainGradedPairing K₁ L M₁)
    (P₂ : CochainChainGradedPairing K₂ M₁ Mᵣ)
    (p q r : ℕ)
    (inputX : L.X ((p + q) + r) ⟶ L.X (p + (q + r)))
    (inputCycles : L.cycles ((p + q) + r) ⟶ L.cycles (p + (q + r)))
    (inputHomology : L.homology ((p + q) + r) ⟶
      L.homology (p + (q + r)))
    (outputX : Mₗ.X r ⟶ Mᵣ.X r)
    (outputCycles : Mₗ.cycles r ⟶ Mᵣ.cycles r)
    (outputHomology : Mₗ.homology r ⟶ Mᵣ.homology r)
    (inputCycles_i : inputCycles ≫ L.iCycles (p + (q + r)) =
      L.iCycles ((p + q) + r) ≫ inputX)
    (input_π : L.homologyπ ((p + q) + r) ≫ inputHomology =
      inputCycles ≫ L.homologyπ (p + (q + r)))
    (outputCycles_i : outputCycles ≫ Mᵣ.iCycles r =
      Mₗ.iCycles r ≫ outputX)
    (output_π : Mₗ.homologyπ r ≫ outputHomology =
      outputCycles ≫ Mᵣ.homologyπ r)
    (hpair :
      (P₁₂.pair p q ⊗ₘ 𝟙 (L.X ((p + q) + r))) ≫
          Pₗ.pair (p + q) r ≫ outputX =
        ((β_ (K₁.X p) (K₂.X q)).hom ⊗ₘ
            𝟙 (L.X ((p + q) + r))) ≫
          (α_ (K₂.X q) (K₁.X p) (L.X ((p + q) + r))).hom ≫
          (𝟙 (K₂.X q) ⊗ₘ
            ((𝟙 (K₁.X p) ⊗ₘ inputX) ≫
              P₁.pair p (q + r))) ≫
          P₂.pair q r) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (L.homology ((p + q) + r))) ≫
        Pₗ.pairHomology (p + q) r ≫ outputHomology =
      ((β_ (K₁.homology p) (K₂.homology q)).hom ⊗ₘ
          𝟙 (L.homology ((p + q) + r))) ≫
        (α_ (K₂.homology q) (K₁.homology p)
          (L.homology ((p + q) + r))).hom ≫
        (𝟙 (K₂.homology q) ⊗ₘ
          ((𝟙 (K₁.homology p) ⊗ₘ inputHomology) ≫
            P₁.pairHomology p (q + r))) ≫
        P₂.pairHomology q r := by
  apply pairHomology_associativity_ordered R P₁₂ Pₗ P₁ P₂ p q r
    inputCycles inputHomology outputHomology input_π
  rw [output_π]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono (Mᵣ.iCycles r)).1
  have hinner :
      ((𝟙 (K₁.cycles p) ⊗ₘ inputCycles) ≫
          P₁.pairCycles p (q + r)) ≫ M₁.iCycles (q + r) =
        (K₁.iCycles p ⊗ₘ L.iCycles ((p + q) + r)) ≫
          (𝟙 (K₁.X p) ⊗ₘ inputX) ≫ P₁.pair p (q + r) := by
    rw [Category.assoc, P₁.pairCycles_i]
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
    rw [inputCycles_i]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    simp
  simp only [Category.assoc]
  rw [outputCycles_i, Pₗ.pairCycles_i_assoc, P₂.pairCycles_i]
  slice_lhs 1 2 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  slice_rhs 3 4 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [P₁₂.pairCycles_i]
  simp only [Category.id_comp]
  rw [hinner]
  have hleftTensor :
      (((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P₁₂.pair p q) ⊗ₘ
          L.iCycles ((p + q) + r)) =
        ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ⊗ₘ
            L.iCycles ((p + q) + r)) ≫
          (P₁₂.pair p q ⊗ₘ 𝟙 (L.X ((p + q) + r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hrightTensor :
      (K₂.iCycles q ⊗ₘ
          ((K₁.iCycles p ⊗ₘ L.iCycles ((p + q) + r)) ≫
            (𝟙 (K₁.X p) ⊗ₘ inputX) ≫ P₁.pair p (q + r))) =
        (K₂.iCycles q ⊗ₘ
            (K₁.iCycles p ⊗ₘ L.iCycles ((p + q) + r))) ≫
          (𝟙 (K₂.X q) ⊗ₘ
            ((𝟙 (K₁.X p) ⊗ₘ inputX) ≫
              P₁.pair p (q + r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hleftTensor, hrightTensor]
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_naturality_assoc]
  slice_rhs 1 2 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  simp only [Category.id_comp]
  rw [← BraidedCategory.braiding_naturality]
  rw [← Category.comp_id (L.iCycles ((p + q) + r))]
  rw [← MonoidalCategory.tensorHom_comp_tensorHom_assoc]
  rw [hpair]
  simp

end HomologicalComplex.CochainChainGradedPairing

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u.
Nonnegative R-module chain complexes carry the monoidal tensor complex with differential
d(x_p⊗y_q)=dx_p⊗y_q+(-1)^p x_p⊗dy_q. The canonical module tensor associator induces its chain
associator, supplying the monoidal structure for the ordered mixed pairing diagrams. -/
noncomputable local instance orderedAssociativityMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u. Let
Δ₁₂:K₁₂→K₁⊗K₂ and μ₁₂:A₁⊗A₂→A₁₂ define the Hom cup product. Let Δ_l:L→K₁₂⊗J_l, Δ₁:L→K₁⊗J₁ and
Δ₂:M₁→K₂⊗J₂, with actions ρ_l,ρ₁,ρ₂ into M_l,M₁,M_r. For p,q,r choose u:L_{(p+q)+r}→L_{p+(q+r)}
and c:M_l,r→M_r,r. If Δ_l≫D_l(φ∪ψ)≫c=u≫Δ₁≫D₁(φ)≫Δ₂≫D₂(ψ) for every φ:K₁,p→A₁ and ψ:K₂,q→A₂, then
c((φ∪ψ)⌢_l x)=ψ⌢₂(φ⌢₁u(x)). The stated tensor identity braids the two cochain factors by the
ordinary module braiding before reassociating them. -/
public theorem linearHomCochainChainPair_associativity_ordered_of_diagrams
    {K₁ K₂ K₁₂ L Jₗ J₁ M₁ J₂ Mₗ Mᵣ :
      ChainComplex (ModuleCat.{u} R) ℕ}
    {A₁ A₂ A₁₂ : ModuleCat.{u} R}
    (Δ₁₂ : K₁₂ ⟶ K₁ ⊗ K₂) (Δₗ : L ⟶ K₁₂ ⊗ Jₗ)
    (Δ₁ : L ⟶ K₁ ⊗ J₁) (Δ₂ : M₁ ⟶ K₂ ⊗ J₂)
    (μ₁₂ : A₁ ⊗ A₂ ⟶ A₁₂)
    (ρₗ : ∀ i, A₁₂ ⊗ Jₗ.X i ⟶ Mₗ.X i)
    (ρ₁ : ∀ i, A₁ ⊗ J₁.X i ⟶ M₁.X i)
    (ρ₂ : ∀ i, A₂ ⊗ J₂.X i ⟶ Mᵣ.X i)
    (p q r : ℕ)
    (inputX : L.X ((p + q) + r) ⟶ L.X (p + (q + r)))
    (outputX : Mₗ.X r ⟶ Mᵣ.X r)
    (hdiagram : ∀ (φ : K₁.X p ⟶ A₁) (ψ : K₂.X q ⟶ A₂),
      Δₗ.f ((p + q) + r) ≫
          linearHomCochainChainPairDesc R ρₗ (p + q) r
            (Δ₁₂.f (p + q) ≫
              linearHomPairingDesc R μ₁₂ p q φ ψ) ≫
          outputX =
        inputX ≫ Δ₁.f (p + (q + r)) ≫
          linearHomCochainChainPairDesc R ρ₁ p (q + r) φ ≫
          Δ₂.f (q + r) ≫
          linearHomCochainChainPairDesc R ρ₂ q r ψ) :
    ((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q ⊗ₘ
          𝟙 (L.X ((p + q) + r))) ≫
        linearHomCochainChainPair R Δₗ ρₗ (p + q) r ≫ outputX =
      ((β_
          (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
            (Opposite.op K₁)).X p)
          (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
            (Opposite.op K₂)).X q)).hom ⊗ₘ
          𝟙 (L.X ((p + q) + r))) ≫
        (α_
          (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
            (Opposite.op K₂)).X q)
          (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
            (Opposite.op K₁)).X p)
          (L.X ((p + q) + r))).hom ≫
        (𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
            (Opposite.op K₂)).X q) ⊗ₘ
          ((𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
              (Opposite.op K₁)).X p) ⊗ₘ inputX) ≫
            linearHomCochainChainPair R Δ₁ ρ₁ p (q + r))) ≫
        linearHomCochainChainPair R Δ₂ ρ₂ q r := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro φ ψ x
  change outputX.hom
      ((linearHomCochainChainPair R Δₗ ρₗ (p + q) r).hom
        (((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q).hom
            (φ ⊗ₜ[R] ψ) ⊗ₜ[R] x)) =
    (linearHomCochainChainPair R Δ₂ ρ₂ q r).hom
      (ψ ⊗ₜ[R]
        (linearHomCochainChainPair R Δ₁ ρ₁ p (q + r)).hom
          (φ ⊗ₜ[R] inputX.hom x))
  erw [linearHomCochainGradedPairing_pair,
    linearHomCochainPair_tmul,
    linearHomCochainChainPair_tmul,
    linearHomCochainChainPair_tmul,
    linearHomCochainChainPair_tmul]
  exact ConcreteCategory.congr_hom (hdiagram φ ψ) x

end HomologicalComplex

end
