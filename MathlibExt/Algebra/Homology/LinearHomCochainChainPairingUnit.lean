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

public import MathlibExt.Algebra.Homology.LinearHomCochainPairingHeterogeneous
public import MathlibExt.Algebra.Homology.LinearHomCochainChainPairing

/-!
# Unit diagrams for degree-lowering linear Hom pairings

Let R be commutative and all coefficient modules lie in universe u. The Hom cochain–chain
descriptor is the heterogeneous Hom-pairing descriptor when the second cochain is the identity
of its chain term. This identifies its degree-zero specialization with the tensor unit action.

Let Δ:K→K_u⊗K and ε:K_u→𝟙 be chain maps satisfying Δ≫(ε⊗id_K)≫λ_K=id_K. For e:𝟙→U and actions
ρ_q:U⊗K_q→K_q with (e⊗id)≫ρ_q=λ_{K_q}, the cochain induced by ε,e acts as a left unit in every
q∈ℕ. The formula includes the identification K_q≅K_{0+q}.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory MonoidalCategory Opposite

universe u

namespace HomologicalComplex

open LinearHomCochainPairingHeterogeneous

variable (R : Type u) [CommRing R]

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
Nonnegative R-module chain complexes carry the monoidal total tensor product, with scalar
single-complex unit and differential d(x_p⊗y_q)=dx_p⊗y_q+(-1)^p x_p⊗dy_q. Its canonical left
unitor is the chain map used in the unit-diagram condition. -/
noncomputable local instance linearHomCochainChainUnitMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
For K₁,K₂,L, A, ρ_q:A⊗K₂,q→L_q and φ:K₁,p→A, the cochain–chain descriptor (K₁⊗K₂)_{p+q}→L_q
equals the heterogeneous Hom pairing descriptor formed from coefficient map ρ_q, cochains φ and
id_{K₂,q}. Both select the same (p,q) summand and act there by (φ⊗id)≫ρ_q. -/
lemma linearHomCochainChainPairDesc_eq_linearHomPairingDesc
    {K₁ K₂ L : ChainComplex (ModuleCat.{u} R) ℕ}
    {A : ModuleCat.{u} R} [HasTensor K₁ K₂]
    (ρ : ∀ q, A ⊗ K₂.X q ⟶ L.X q) (p q : ℕ) (φ : K₁.X p ⟶ A) :
    linearHomCochainChainPairDesc R ρ p q φ =
      linearHomPairingDesc R (ρ q) p q φ (𝟙 (K₂.X q)) := by
  apply mapBifunctor.hom_ext
  intro i j h
  unfold linearHomCochainChainPairDesc
  rw [ι_mapBifunctorDesc, ιTensorObj_comp_linearHomPairingDesc]
  by_cases hi : i = p
  · subst i
    have hj : j = q := Nat.add_left_cancel h
    subst j
    simp
  · simp [hi]

/-- Let R be commutative in universe u, with all modules and nonnegative chain-complex terms in u.
Let Δ:K→K_u⊗K, ε:K_u→𝟙 satisfy Δ≫(ε⊗id_K)≫λ_K=id_K, and let e:𝟙→U with actions ρ_q:U⊗K_q→K_q
satisfy (e⊗id_{K_q})≫ρ_q=λ_{K_q}. The canonical map η:𝟙→Hom_R((K_u)_0,U) induced by ε and e is a
left unit for the degree-(0,q) cap pairing: (η⊗id_{K_q}) followed by K_q≅K_{0+q} and
κ_{Δ,ρ}^{0,q} equals λ_{K_q}, for every q∈ℕ. -/
theorem linearHomCochainChainPair_left_unit_of_diagrams
    {Kᵤ K : ChainComplex (ModuleCat.{u} R) ℕ}
    {U : ModuleCat.{u} R}
    (Δ : K ⟶ tensorObj Kᵤ K)
    (ε : Kᵤ ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (e : 𝟙_ (ModuleCat.{u} R) ⟶ U)
    (ρ : ∀ q, U ⊗ K.X q ⟶ K.X q)
    (hΔ : Δ ≫ tensorHom ε (𝟙 K) ≫ (leftUnitor K).hom = 𝟙 K)
    (hρ : ∀ q, (e ▷ K.X q) ≫ ρ q = (λ_ (K.X q)).hom)
    (q : ℕ) :
    (linearHomCochainUnitOfCounitHom R Kᵤ ε U e ▷ K.X q) ≫
        (𝟙 _ ⊗ₘ (K.XIsoOfEq (Nat.zero_add q)).inv) ≫
        linearHomCochainChainPair R Δ ρ 0 q =
      (λ_ (K.X q)).hom := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a x
  change R at a
  change (linearHomCochainChainPair R Δ ρ 0 q).hom
      ((a • linearHomCochainUnitOfCounit R Kᵤ ε U e) ⊗ₜ[R]
        ((K.XIsoOfEq (Nat.zero_add q)).inv).hom x) = a • x
  rw [← TensorProduct.smul_tmul']
  rw [map_smul]
  congr 1
  rw [linearHomCochainChainPair_tmul,
    linearHomCochainChainPairDesc_eq_linearHomPairingDesc]
  have htransport {m n : ℕ} (h : m = n) :
      (K.XIsoOfEq h).inv = (K.XIsoOfEq h.symm).hom := by
    subst n
    rfl
  have hdesc := heterogeneousLinearHomPairingDesc_left_unit R ε e (ρ q)
    (𝟙 (K.X q)) (by simpa using hρ q) q (𝟙 (K.X q))
  simp only [Category.comp_id] at hdesc
  have hmain :
      (K.XIsoOfEq (Nat.zero_add q)).inv ≫ Δ.f (0 + q) ≫
          linearHomPairingDesc R (ρ q) 0 q
            (linearHomCochainUnitOfCounit R Kᵤ ε U e) (𝟙 (K.X q)) =
        𝟙 (K.X q) := by
    rw [htransport]
    rw [XIsoOfEq_comp_heterogeneousLinearHomPairingDesc R Δ (ρ q)
      0 q q (Nat.zero_add q).symm
      (linearHomCochainUnitOfCounit R Kᵤ ε U e) (𝟙 (K.X q))]
    rw [hdesc]
    have hΔq := congrArg (fun f => f.f q) hΔ
    dsimp only [HomologicalComplex.comp_f] at hΔq
    change Δ.f q ≫ (ε ▷ K).f q ≫ (λ_ K).hom.f q = 𝟙 (K.X q) at hΔq
    exact hΔq
  exact ConcreteCategory.congr_hom hmain x

end HomologicalComplex

end
