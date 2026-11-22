/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.WittVector.GradedCartierModuleData
public import MathlibExt.RingTheory.WittVector.GradedCartierNModule
public import MathlibExt.RingTheory.WittVector.CartierLift

@[expose] public section

universe w

namespace CerednikDrinfeld

variable {p : ℕ} [Fact p.Prime]

/-- The characterization of multiplication by `p`, at an arbitrary
universe for the coefficient ring. -/
example {B : Type w} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p j) (x : D.M) :
    (p : ℕ) • x = D.frobenius (D.verschiebung x) :=
  D.natCast_smul_eq_frobenius_verschiebung x

/-- A homogeneous `V`-basis forces Verschiebung to be injective. -/
example {B : Type} [CommRing B] {j : Zp2 p →+* B}
    {D : GradedCartierModuleData p j} {γ : Fin 2 → D.M}
    (h : D.IsHomogeneousVBasis γ) : Function.Injective D.verschiebung :=
  h.verschiebung_injective

/-- The defining relation of the `N`-module quotient. -/
example {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p j) (m : D.M) :
    D.nMk (D.verschiebung m, -D.varpi m) = 0 :=
  D.nMk_verschiebung_neg_varpi m

/-- The map `lambda` on generators of the `N`-module. -/
example {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p j) (m m' : D.M) :
    D.lambda (D.nMk (m, m')) = D.varpi m + D.verschiebung m' :=
  D.lambda_nMk m m'

/-- The chosen canonical `L`-map is canonical. -/
example {B : Type} [CommRing B] {j : Zp2 p →+* B}
    (D : GradedCartierModuleData p j)
    (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) :
    D.IsCanonicalLMap (D.cartierL h) :=
  D.cartierL_spec h

/-- The lift homomorphism is surjective, and the lifted constants multiply
to `p` at order zero. -/
example {B : Type} [CommRing B] (j : Zp2 p →+* B) (u v : B) (huv : u * v = p) :
    Function.Surjective (CartierLift.liftHom j u v huv) :=
  CartierLift.liftHom_surjective j u v huv

example (a : ℕ → Fin 2 → Zp2 p) :
    CartierLift.liftConstants (p := p) (R := Zp2 p) a 0 0 *
      CartierLift.liftConstants (p := p) (R := Zp2 p) a 0 1 = p :=
  CartierLift.liftConstants_zero_zero_mul a

section ProdExample

/-- The coefficient action of Witt vectors on the field with `p ^ 2`
elements, through the constant coefficient. -/
noncomputable instance : Module (WittVector p (GaloisField p 2)) (GaloisField p 2) :=
  Module.compHom _ WittVector.constantCoeff

/-- Frobenius on each factor, with the two factors exchanged. -/
noncomputable def frobSwap : (GaloisField p 2 × GaloisField p 2) →+
    (GaloisField p 2 × GaloisField p 2) where
  toFun x := (x.2 ^ p, x.1 ^ p)
  map_zero' := by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    simp [zero_pow hp.ne']
  map_add' x y := Prod.ext (add_pow_char _ _ _) (add_pow_char _ _ _)

/-- A nonzero graded Cartier module on two copies of the field with
`p ^ 2` elements: Frobenius exchanges the factors and raises to the
`p`-th power, Verschiebung and the uniformizer vanish, and the graded
pieces are the two coordinate axes. -/
noncomputable def prodData :
    GradedCartierModuleData p
      (WittVector.constantCoeff :
        WittVector p (GaloisField p 2) →+* GaloisField p 2) where
  M := GaloisField p 2 × GaloisField p 2
  frobenius := frobSwap
  verschiebung := 0
  varpi := 0
  piece := fun i =>
    if i = 0 then LinearMap.range (LinearMap.inl _ _ _)
    else LinearMap.range (LinearMap.inr _ _ _)
  frobenius_smul := by
    intro w x
    apply Prod.ext
    · show (WittVector.constantCoeff w * x.2) ^ p =
        WittVector.constantCoeff (WittVector.frobenius w) * (x.2 ^ p)
      rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, mul_pow]
    · show (WittVector.constantCoeff w * x.1) ^ p =
        WittVector.constantCoeff (WittVector.frobenius w) * (x.1 ^ p)
      rw [WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
        WittVector.coeff_frobenius_charP, mul_pow]
  smul_verschiebung := by simp
  verschiebung_smul_frobenius := by
    intro w x
    simp only [AddMonoidHom.zero_apply]
    apply Prod.ext
    · show (0 : GaloisField p 2) =
        WittVector.constantCoeff (WittVector.verschiebung w) * x.1
      rw [WittVector.constantCoeff_apply, WittVector.verschiebung_coeff_zero,
        zero_mul]
    · show (0 : GaloisField p 2) =
        WittVector.constantCoeff (WittVector.verschiebung w) * x.2
      rw [WittVector.constantCoeff_apply, WittVector.verschiebung_coeff_zero,
        zero_mul]
  frobenius_verschiebung := by
    intro x
    simp only [AddMonoidHom.zero_apply, map_zero]
    apply Prod.ext <;> simp [nsmul_eq_mul]
  varpi_verschiebung := by simp
  varpi_frobenius := by simp
  varpi_varpi := by
    intro x
    simp only [LinearMap.zero_apply]
    apply Prod.ext <;> simp [nsmul_eq_mul]
  isCompl_piece := LinearMap.isCompl_range_inl_inr
  verschiebung_mem := by simp
  frobenius_mem := by
    intro i x hx
    have hp : 0 < p := (Fact.out : p.Prime).pos
    fin_cases i
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨a ^ p, by
        simp only [frobSwap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          LinearMap.inr_apply]
        exact Prod.ext (by simp [zero_pow hp.ne']) rfl⟩
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨a ^ p, by
        simp only [frobSwap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
          LinearMap.inl_apply]
        exact Prod.ext rfl (by simp [zero_pow hp.ne'])⟩
  varpi_mem := by simp

/-- The example is nonzero: its underlying module has distinct elements. -/
example : Nontrivial (prodData (p := p)).M :=
  inferInstanceAs (Nontrivial (GaloisField p 2 × GaloisField p 2))

/-- Frobenius in the example is the Frobenius swap, not the zero map. -/
example (a : GaloisField p 2) :
    (prodData (p := p)).frobenius (a, 0) = (0, a ^ p) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  show frobSwap (a, 0) = (0, a ^ p)
  apply Prod.ext
  · show (0 : GaloisField p 2) ^ p = 0
    exact zero_pow hp.ne'
  · rfl

/-- The relation and `lambda` computations in the example. -/
example (m : (prodData (p := p)).M) :
    (prodData (p := p)).nMk ((prodData (p := p)).verschiebung m, 0) = 0 := by
  have hv : (prodData (p := p)).varpi m = 0 := by
    show (0 : (prodData (p := p)).M) = 0
    rfl
  have h := (prodData (p := p)).nMk_verschiebung_neg_varpi m
  rwa [hv, neg_zero] at h

example (m m' : (prodData (p := p)).M) :
    (prodData (p := p)).lambda ((prodData (p := p)).nMk (m, m')) =
      (prodData (p := p)).verschiebung m' := by
  rw [(prodData (p := p)).lambda_nMk]
  show (0 : (prodData (p := p)).M) + (0 : (prodData (p := p)).M) =
    (0 : (prodData (p := p)).M)
  exact add_zero _

/-- Structure constants exist at order zero in the example. -/
example (γ : Fin 2 → (prodData (p := p)).M)
    (a : ℕ → Fin 2 → GaloisField p 2) (i : Fin 2) :
    ∃ h : (prodData (p := p)).M, (prodData (p := p)).varpi (γ i) =
      (∑ m : Fin 0, (⇑(prodData (p := p)).verschiebung)^[(m : ℕ)]
        (WittVector.teichmuller p (a m i) •
          γ (GradedCartierModuleData.piIndex m i))) +
        (⇑(prodData (p := p)).verschiebung)^[0] h :=
  (prodData (p := p)).hasStructureConstants_order_zero γ a i

end ProdExample

end CerednikDrinfeld
