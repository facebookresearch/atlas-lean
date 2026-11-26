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

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyLaws
public import MathlibExt.Algebra.Homology.CochainChainGradedPairingHomology
public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing
/-!
# Mixed cup–cap associativity through compatible comparisons

Let R be commutative and all modules lie in universe u. A cochain graded product P₁₂ and mixed
pairings P_l,P₂₃,P_r give the two composites (a∪b)⌢_l z and a⌢_r(b⌢₂₃ z). For p,q,r∈ℕ, the chain
input degrees are (p+q)+r and q+(p+r), and both outputs have degree r. The declarations allow
specified input maps between these degrees and specified output maps between different target
complexes.

A mixed associativity equation on cycles, together with compatibility of the input cycle and
homology maps, descends to the corresponding homology equation. A stronger termwise equation
descends when both input and output maps also commute with cycles inclusions and homology
projections. For linear Hom cochains, a componentwise equation involving the four chain
diagonals and coefficient actions gives the underlying mixed associativity identity.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace HomologicalComplex.CochainChainGradedPairing

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u. For a
cochain–chain graded pairing P:K⊗L→M with K a nonnegative cochain complex and L,M chain
complexes, p,q∈ℕ, x∈Z^pK and y∈Z_{p+q}L, its homology pairing satisfies P_H([x]⊗[y])=[P_Z(x⊗y)]
in H_qM. The source is H^pK⊗H_{p+q}L, and the brackets are the canonical homology projections. -/
@[simp]
lemma pairHomology_π_apply
    {K : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M : ChainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainChainGradedPairing K L M) (p q : ℕ)
    (x : K.cycles p) (y : L.cycles (p + q)) :
    (P.pairHomology p q).hom
        ((K.homologyπ p).hom x ⊗ₜ[R] (L.homologyπ (p + q)).hom y) =
      (M.homologyπ q).hom ((P.pairCycles p q).hom (x ⊗ₜ[R] y)) := by
  exact ConcreteCategory.congr_hom
    (tensor_homologyπ_comp_pairHomology P p q) (x ⊗ₜ[R] y)

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u. Let
P₁₂:K₁,K₂→K₁₂ be a cochain graded pairing and P_l:K₁₂,L→M_l, P₂₃:K₂,L→M₂₃, P_r:K₁,M₂₃→M_r mixed
pairings. For p,q,r∈ℕ put n=(p+q)+r and n′=q+(p+r). Given u_Z:Z_nL→Z_{n′}L, u_H:H_nL→H_{n′}L
with π_n≫u_H=u_Z≫π_{n′}, and c:H_rM_l→H_rM_r, suppose
c([P_l^Z(P₁₂^Z(x,y),z)])=[P_r^Z(x,P₂₃^Z(y,u_Zz))] for all cycles x,y,z in degrees p,q,n. Then
c((a∪_{12}b)⌢_l t)=a⌢_r(b⌢₂₃u_H(t)) for homology classes a,b,t. The tensor-map equation includes
the ordinary module associator. -/
theorem pairHomology_associativity
    {K₁ K₂ K₁₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M₂₃ Mₗ Mᵣ : ChainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainChainGradedPairing K₁₂ L Mₗ)
    (P₂₃ : CochainChainGradedPairing K₂ L M₂₃)
    (Pᵣ : CochainChainGradedPairing K₁ M₂₃ Mᵣ)
    (p q r : ℕ)
    (inputCycles : L.cycles ((p + q) + r) ⟶ L.cycles (q + (p + r)))
    (input : L.homology ((p + q) + r) ⟶ L.homology (q + (p + r)))
    (comparison : Mₗ.homology r ⟶ Mᵣ.homology r)
    (input_π : L.homologyπ ((p + q) + r) ≫ input =
      inputCycles ≫ L.homologyπ (q + (p + r)))
    (hcycles :
      (P₁₂.pairCycles p q ⊗ₘ 𝟙 (L.cycles ((p + q) + r))) ≫
          Pₗ.pairCycles (p + q) r ≫ Mₗ.homologyπ r ≫ comparison =
        (α_ (K₁.cycles p) (K₂.cycles q)
          (L.cycles ((p + q) + r))).hom ≫
          (𝟙 (K₁.cycles p) ⊗ₘ
            ((𝟙 (K₂.cycles q) ⊗ₘ inputCycles) ≫
              P₂₃.pairCycles q (p + r))) ≫
          Pᵣ.pairCycles p r ≫ Mᵣ.homologyπ r) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (L.homology ((p + q) + r))) ≫
        Pₗ.pairHomology (p + q) r ≫ comparison =
      (α_ (K₁.homology p) (K₂.homology q)
        (L.homology ((p + q) + r))).hom ≫
        (𝟙 (K₁.homology p) ⊗ₘ
          ((𝟙 (K₂.homology q) ⊗ₘ input) ≫
            P₂₃.pairHomology q (p + r))) ≫
        Pᵣ.pairHomology p r := by
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
    (Pᵣ.pairHomology p r).hom
      ((K₁.homologyπ p).hom x₀ ⊗ₜ[R]
        (P₂₃.pairHomology q (p + r)).hom
          ((K₂.homologyπ q).hom y₀ ⊗ₜ[R]
            input.hom ((L.homologyπ ((p + q) + r)).hom z₀)))
  rw [HomologicalComplex.CochainGradedPairing.pairHomology_π_apply R P₁₂,
    pairHomology_π_apply R Pₗ]
  have hinput := ConcreteCategory.congr_hom input_π z₀
  change input.hom ((L.homologyπ ((p + q) + r)).hom z₀) =
    (L.homologyπ (q + (p + r))).hom (inputCycles.hom z₀) at hinput
  rw [hinput, pairHomology_π_apply R P₂₃, pairHomology_π_apply R Pᵣ]
  exact ConcreteCategory.congr_hom hcycles
    ((x₀ ⊗ₜ[R] y₀) ⊗ₜ[R] z₀)

/-- Let R be commutative in universe u. Let K₁,K₂,K₁₂ be nonnegative cochain complexes and
L,M₂₃,M_l,M_r nonnegative chain complexes of R-modules with carriers in u. Let P₁₂ pair K₁,K₂
into K₁₂, and let P_l:K₁₂,L→M_l, P₂₃:K₂,L→M₂₃ and P_r:K₁,M₂₃→M_r be mixed graded pairings. For
p,q,r∈ℕ put n=(p+q)+r and n′=q+(p+r).

Choose degreewise maps u_X:L_n→L_{n′}, u_Z:Z_nL→Z_{n′}L, u_H:H_nL→H_{n′}L and
c_X:(M_l)_r→(M_r)_r, c_Z:Z_rM_l→Z_rM_r, c_H:H_rM_l→H_rM_r. Assume u_Z≫i_{L,n′}=i_{L,n}≫u_X,
π_{L,n}≫u_H=u_Z≫π_{L,n′}, c_Z≫i_{M_r,r}=i_{M_l,r}≫c_X and π_{M_l,r}≫c_H=c_Z≫π_{M_r,r}.

If c_X(P_l(P₁₂(x,y),z))=P_r(x,P₂₃(y,u_Xz)) on terms of degrees p,q,n, then c_H((a∪_{12}b)⌢_l
t)=a⌢_r(b⌢₂₃u_H(t)) on cohomology and homology classes. The tensor-map equality uses the
canonical module associator. -/
theorem pairHomology_associativity_of_pair
    {K₁ K₂ K₁₂ : CochainComplex (ModuleCat.{u} R) ℕ}
    {L M₂₃ Mₗ Mᵣ : ChainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainChainGradedPairing K₁₂ L Mₗ)
    (P₂₃ : CochainChainGradedPairing K₂ L M₂₃)
    (Pᵣ : CochainChainGradedPairing K₁ M₂₃ Mᵣ)
    (p q r : ℕ)
    (inputX : L.X ((p + q) + r) ⟶ L.X (q + (p + r)))
    (inputCycles : L.cycles ((p + q) + r) ⟶ L.cycles (q + (p + r)))
    (inputHomology : L.homology ((p + q) + r) ⟶
      L.homology (q + (p + r)))
    (outputX : Mₗ.X r ⟶ Mᵣ.X r)
    (outputCycles : Mₗ.cycles r ⟶ Mᵣ.cycles r)
    (outputHomology : Mₗ.homology r ⟶ Mᵣ.homology r)
    (inputCycles_i : inputCycles ≫ L.iCycles (q + (p + r)) =
      L.iCycles ((p + q) + r) ≫ inputX)
    (input_π : L.homologyπ ((p + q) + r) ≫ inputHomology =
      inputCycles ≫ L.homologyπ (q + (p + r)))
    (outputCycles_i : outputCycles ≫ Mᵣ.iCycles r =
      Mₗ.iCycles r ≫ outputX)
    (output_π : Mₗ.homologyπ r ≫ outputHomology =
      outputCycles ≫ Mᵣ.homologyπ r)
    (hpair :
      (P₁₂.pair p q ⊗ₘ 𝟙 (L.X ((p + q) + r))) ≫
          Pₗ.pair (p + q) r ≫ outputX =
        (α_ (K₁.X p) (K₂.X q) (L.X ((p + q) + r))).hom ≫
          (𝟙 (K₁.X p) ⊗ₘ
            ((𝟙 (K₂.X q) ⊗ₘ inputX) ≫
              P₂₃.pair q (p + r))) ≫
          Pᵣ.pair p r) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (L.homology ((p + q) + r))) ≫
        Pₗ.pairHomology (p + q) r ≫ outputHomology =
      (α_ (K₁.homology p) (K₂.homology q)
        (L.homology ((p + q) + r))).hom ≫
        (𝟙 (K₁.homology p) ⊗ₘ
          ((𝟙 (K₂.homology q) ⊗ₘ inputHomology) ≫
            P₂₃.pairHomology q (p + r))) ≫
        Pᵣ.pairHomology p r := by
  apply pairHomology_associativity R P₁₂ Pₗ P₂₃ Pᵣ p q r
    inputCycles inputHomology outputHomology input_π
  rw [output_π]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono (Mᵣ.iCycles r)).1
  have hrightInner :
      ((𝟙 (K₂.cycles q) ⊗ₘ inputCycles) ≫
          P₂₃.pairCycles q (p + r)) ≫ M₂₃.iCycles (p + r) =
        (K₂.iCycles q ⊗ₘ L.iCycles ((p + q) + r)) ≫
          (𝟙 (K₂.X q) ⊗ₘ inputX) ≫ P₂₃.pair q (p + r) := by
    rw [Category.assoc, P₂₃.pairCycles_i]
    rw [← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom]
    simp only [Category.id_comp]
    rw [inputCycles_i]
    rw [MonoidalCategory.tensorHom_comp_tensorHom_assoc]
    simp
  simp only [Category.assoc]
  rw [outputCycles_i, Pₗ.pairCycles_i_assoc, Pᵣ.pairCycles_i]
  slice_lhs 1 2 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  slice_rhs 2 3 =>
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [P₁₂.pairCycles_i]
  simp only [Category.id_comp]
  rw [hrightInner]
  have hleftTensor :
      (((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P₁₂.pair p q) ⊗ₘ
          L.iCycles ((p + q) + r)) =
        ((K₁.iCycles p ⊗ₘ K₂.iCycles q) ⊗ₘ
            L.iCycles ((p + q) + r)) ≫
          (P₁₂.pair p q ⊗ₘ 𝟙 (L.X ((p + q) + r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hrightTensor :
      (K₁.iCycles p ⊗ₘ
          ((K₂.iCycles q ⊗ₘ L.iCycles ((p + q) + r)) ≫
            (𝟙 (K₂.X q) ⊗ₘ inputX) ≫ P₂₃.pair q (p + r))) =
        (K₁.iCycles p ⊗ₘ
            (K₂.iCycles q ⊗ₘ L.iCycles ((p + q) + r))) ≫
          (𝟙 (K₁.X p) ⊗ₘ
            ((𝟙 (K₂.X q) ⊗ₘ inputX) ≫
              P₂₃.pair q (p + r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hleftTensor, hrightTensor]
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_naturality_assoc]
  rw [hpair]

end HomologicalComplex.CochainChainGradedPairing

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u. The
category of R-module-valued chain complexes of shape down ℕ is monoidal under the total tensor
complex. Its homogeneous differential is d(x_p⊗y_q)=dx_p⊗y_q+(-1)^p x_p⊗dy_q, and its associator
is the canonical tensor associator. This is the tensor structure used in the mixed associativity
diagrams. -/
noncomputable local instance mixedAssociativityMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Let R be commutative in universe u, with all coefficient modules and complex terms in u. Let
Δ₁₂:K₁₂→K₁⊗K₂ and μ₁₂:A₁⊗A₂→A₁₂ define the Hom cochain cup product. Let Δ_l:L→K₁₂⊗J_l,
Δ₂₃:L→K₂⊗J₂₃ and Δ_r:M₂₃→K₁⊗J_r, with actions ρ_l:A₁₂⊗J_l→M_l, ρ₂₃:A₂⊗J₂₃→M₂₃ and
ρ_r:A₁⊗J_r→M_r. For p,q,r, input u:L_{(p+q)+r}→L_{q+(p+r)} and output c:M_l,r→M_r,r, assume for
every φ:K₁,p→A₁ and ψ:K₂,q→A₂ the descriptor equation Δ_l≫D_l(φ∪ψ)≫c=u≫Δ₂₃≫D₂₃(ψ)≫Δ_r≫D_r(φ).
Then c((φ∪ψ)⌢_l x)=φ⌢_r(ψ⌢₂₃u(x)) as the mixed tensor pairing identity, including the module
associator. -/
public theorem linearHomCochainChainPair_associativity_of_diagrams
    {K₁ K₂ K₁₂ L Jₗ J₂₃ M₂₃ Jᵣ Mₗ Mᵣ :
      ChainComplex (ModuleCat.{u} R) ℕ}
    {A₁ A₂ A₁₂ : ModuleCat.{u} R}
    (Δ₁₂ : K₁₂ ⟶ K₁ ⊗ K₂) (Δₗ : L ⟶ K₁₂ ⊗ Jₗ)
    (Δ₂₃ : L ⟶ K₂ ⊗ J₂₃) (Δᵣ : M₂₃ ⟶ K₁ ⊗ Jᵣ)
    (μ₁₂ : A₁ ⊗ A₂ ⟶ A₁₂)
    (ρₗ : ∀ i, A₁₂ ⊗ Jₗ.X i ⟶ Mₗ.X i)
    (ρ₂₃ : ∀ i, A₂ ⊗ J₂₃.X i ⟶ M₂₃.X i)
    (ρᵣ : ∀ i, A₁ ⊗ Jᵣ.X i ⟶ Mᵣ.X i)
    (p q r : ℕ)
    (inputX : L.X ((p + q) + r) ⟶ L.X (q + (p + r)))
    (outputX : Mₗ.X r ⟶ Mᵣ.X r)
    (hdiagram : ∀ (φ : K₁.X p ⟶ A₁) (ψ : K₂.X q ⟶ A₂),
      Δₗ.f ((p + q) + r) ≫
          linearHomCochainChainPairDesc R ρₗ (p + q) r
            (Δ₁₂.f (p + q) ≫
              linearHomPairingDesc R μ₁₂ p q φ ψ) ≫
          outputX =
        inputX ≫ Δ₂₃.f (q + (p + r)) ≫
          linearHomCochainChainPairDesc R ρ₂₃ q (p + r) ψ ≫
          Δᵣ.f (p + r) ≫
          linearHomCochainChainPairDesc R ρᵣ p r φ) :
    ((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q ⊗ₘ
          𝟙 (L.X ((p + q) + r))) ≫
        linearHomCochainChainPair R Δₗ ρₗ (p + q) r ≫ outputX =
      (α_ (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
          (Opposite.op K₁)).X p)
        (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
          (Opposite.op K₂)).X q)
        (L.X ((p + q) + r))).hom ≫
        (𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₁).obj
            (Opposite.op K₁)).X p) ⊗ₘ
          ((𝟙 (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A₂).obj
              (Opposite.op K₂)).X q) ⊗ₘ inputX) ≫
            linearHomCochainChainPair R Δ₂₃ ρ₂₃ q (p + r))) ≫
        linearHomCochainChainPair R Δᵣ ρᵣ p r := by
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro φ ψ x
  change outputX.hom
      ((linearHomCochainChainPair R Δₗ ρₗ (p + q) r).hom
        (((linearHomCochainGradedPairing R Δ₁₂ μ₁₂).pair p q).hom
            (φ ⊗ₜ[R] ψ) ⊗ₜ[R] x)) =
    (linearHomCochainChainPair R Δᵣ ρᵣ p r).hom
      (φ ⊗ₜ[R]
        (linearHomCochainChainPair R Δ₂₃ ρ₂₃ q (p + r)).hom
          (ψ ⊗ₜ[R] inputX.hom x))
  erw [linearHomCochainGradedPairing_pair,
    linearHomCochainPair_tmul,
    linearHomCochainChainPair_tmul,
    linearHomCochainChainPair_tmul,
    linearHomCochainChainPair_tmul]
  exact ConcreteCategory.congr_hom (hdiagram φ ψ) x

end HomologicalComplex
end
