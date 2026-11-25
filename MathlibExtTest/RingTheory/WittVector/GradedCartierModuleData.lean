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

section SeqExample

open GradedCartierModuleData

private theorem smul_eq_constantCoeff_mul (w : Zp2 p) (y : GaloisField p 2) :
    w • y = WittVector.constantCoeff w * y :=
  rfl

private theorem pow_p_pow_p (x : GaloisField p 2) : (x ^ p) ^ p = x := by
  have : Fintype (GaloisField p 2) := Fintype.ofFinite _
  rw [← pow_mul, ← sq, ← GaloisField.card p 2 two_ne_zero,
    Nat.card_eq_fintype_card, FiniteField.pow_card]

/-- The sequence `1, 0, 0, ...`. -/
private noncomputable def seqOne : ℕ → GaloisField p 2
  | 0 => 1
  | _ + 1 => 0

/-- Shift a sequence one place to the right, raising each entry to the
`p`-th power. -/
private noncomputable def shiftFrob (s : ℕ → GaloisField p 2) :
    ℕ → GaloisField p 2
  | 0 => 0
  | n + 1 => s n ^ p

/-- `shiftFrob` as an additive map. -/
private noncomputable def shiftFrobHom :
    (ℕ → GaloisField p 2) →+ (ℕ → GaloisField p 2) where
  toFun := shiftFrob
  map_zero' := by
    funext n
    cases n with
    | zero => rfl
    | succ n => exact zero_pow (Fact.out : p.Prime).ne_zero
  map_add' s t := by
    funext n
    cases n with
    | zero => exact (add_zero 0).symm
    | succ n => exact add_pow_char _ _ _

private theorem smul_shiftFrob (w : Zp2 p) (s : ℕ → GaloisField p 2) :
    w • shiftFrob s = shiftFrob (WittVector.frobenius w • s) := by
  funext n
  cases n with
  | zero => exact smul_zero w
  | succ n =>
    change WittVector.constantCoeff w * s n ^ p =
      (WittVector.constantCoeff (WittVector.frobenius w) * s n) ^ p
    rw [mul_pow, WittVector.constantCoeff_apply, WittVector.constantCoeff_apply,
      WittVector.coeff_frobenius_charP, pow_p_pow_p]

/-- Verschiebung of the sequence model: exchange the two copies and apply
`shiftFrob`. -/
private noncomputable def seqV :
    ((ℕ → GaloisField p 2) × (ℕ → GaloisField p 2)) →+
      ((ℕ → GaloisField p 2) × (ℕ → GaloisField p 2)) where
  toFun x := (shiftFrobHom x.2, shiftFrobHom x.1)
  map_zero' := by simp
  map_add' x y := by simp

/-- A graded Cartier module with a homogeneous `V`-basis, over any
coefficient map `j`: two copies of the sequences in the field with `p ^ 2`
elements, Witt vectors acting through the constant coefficient, Verschiebung
exchanging the copies and shifting with a Frobenius twist, and Frobenius and
the uniformizer zero. No field mentions `j`. -/
private noncomputable abbrev seqData (j : Zp2 p →+* GaloisField p 2) :
    GradedCartierModuleData p j where
  M := (ℕ → GaloisField p 2) × (ℕ → GaloisField p 2)
  frobenius := 0
  verschiebung := seqV
  varpi := 0
  piece := fun i =>
    if i = 0 then LinearMap.range (LinearMap.inl _ _ _)
    else LinearMap.range (LinearMap.inr _ _ _)
  frobenius_smul := by simp
  smul_verschiebung w x :=
    Prod.ext (smul_shiftFrob w x.2) (smul_shiftFrob w x.1)
  verschiebung_smul_frobenius := by
    intro w x
    simp only [AddMonoidHom.zero_apply, smul_zero, map_zero]
    refine Prod.ext (funext fun n => ?_) (funext fun n => ?_) <;>
    · change (0 : GaloisField p 2) =
        WittVector.constantCoeff (WittVector.verschiebung w) * _
      rw [WittVector.constantCoeff_apply, WittVector.verschiebung_coeff_zero,
        zero_mul]
  frobenius_verschiebung := by
    intro x
    refine Prod.ext (funext fun n => ?_) (funext fun n => ?_) <;>
      simp [nsmul_eq_mul]
  varpi_verschiebung := by simp
  varpi_frobenius := by simp
  varpi_varpi := by
    intro x
    refine Prod.ext (funext fun n => ?_) (funext fun n => ?_) <;>
      simp [nsmul_eq_mul]
  isCompl_piece := LinearMap.isCompl_range_inl_inr
  verschiebung_mem := by
    intro i x hx
    fin_cases i
    · obtain ⟨a, rfl⟩ := hx
      exact ⟨shiftFrob a, Prod.ext (map_zero shiftFrobHom).symm rfl⟩
    · obtain ⟨b, rfl⟩ := hx
      exact ⟨shiftFrob b, Prod.ext rfl (map_zero shiftFrobHom).symm⟩
  frobenius_mem := by simp
  varpi_mem := by simp

/-- The homogeneous `V`-basis of `seqData`. -/
private noncomputable def seqBasis (j : Zp2 p →+* GaloisField p 2) :
    Fin 2 → (seqData j).M :=
  ![(seqOne, 0), (0, seqOne)]

private theorem seqData_expand (j : Zp2 p →+* GaloisField p 2)
    (cy : (Fin 2 → GaloisField p 2) × (seqData j).M) (n : ℕ) :
    ((∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • seqBasis j i) +
        (seqData j).verschiebung cy.2).1 n =
      cy.1 0 * seqOne n + shiftFrob cy.2.2 n ∧
    ((∑ i : Fin 2, WittVector.teichmuller p (cy.1 i) • seqBasis j i) +
        (seqData j).verschiebung cy.2).2 n =
      cy.1 1 * seqOne n + shiftFrob cy.2.1 n := by
  constructor <;>
  · rw [Fin.sum_univ_two]
    simp [seqBasis, seqV, smul_eq_constantCoeff_mul,
      WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
    rfl

private theorem seqData_isHomogeneousVBasis (j : Zp2 p →+* GaloisField p 2) :
    (seqData j).IsHomogeneousVBasis (seqBasis j) := by
  refine ⟨fun i => ?_, fun x => ?_⟩
  · fin_cases i
    · exact ⟨seqOne, rfl⟩
    · exact ⟨seqOne, rfl⟩
  refine ⟨(![x.1 0, x.2 0],
    (fun n => x.2 (n + 1) ^ p, fun n => x.1 (n + 1) ^ p)), ?_, ?_⟩
  · refine Prod.ext (funext fun n => ?_) (funext fun n => ?_)
    · rw [(seqData_expand j _ n).1]
      cases n with
      | zero => simp [seqOne, shiftFrob]
      | succ n => simp [seqOne, shiftFrob, pow_p_pow_p]
    · rw [(seqData_expand j _ n).2]
      cases n with
      | zero => simp [seqOne, shiftFrob]
      | succ n => simp [seqOne, shiftFrob, pow_p_pow_p]
  · rintro ⟨c, y⟩ h
    have h1 n := (seqData_expand j (c, y) n).1
    have h2 n := (seqData_expand j (c, y) n).2
    rw [← h] at h1 h2
    have h10 := h1 0
    have h20 := h2 0
    simp only [seqOne, shiftFrob, mul_one, add_zero] at h10 h20
    refine Prod.ext (funext fun i => ?_)
      (Prod.ext (funext fun n => ?_) (funext fun n => ?_))
    · fin_cases i
      · exact h10.symm
      · exact h20.symm
    · have h21 := h2 (n + 1)
      simp only [seqOne, shiftFrob, mul_zero, zero_add] at h21
      simp [h21, pow_p_pow_p]
    · have h11 := h1 (n + 1)
      simp only [seqOne, shiftFrob, mul_zero, zero_add] at h11
      simp [h11, pow_p_pow_p]

/-- The clauses of `IsBaseChangeAlong'` other than the coefficient-map
equation, kept only as a boundary probe. -/
private def UnconstrainedBaseChange {B B' : Type} [CommRing B] [CommRing B']
    {j : Zp2 p →+* B} {j' : Zp2 p →+* B'} (φ : B →+* B')
    (D : GradedCartierModuleData p j) (D' : GradedCartierModuleData p j')
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧
    D'.IsHomogeneousVBasis (fun i => f (γ i)))

/-- `IsBaseChangeAlong'` is the coefficient-map equation together with the
unconstrained clauses. -/
example {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B}
    {j' : Zp2 p →+* B'} (φ : B →+* B') (D : GradedCartierModuleData p j)
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M) :
    IsBaseChangeAlong' φ D D' f ↔
      j' = φ.comp j ∧ UnconstrainedBaseChange φ D D' f :=
  Iff.rfl

/-- The coefficient-map clause, read off a base change. -/
example {B B' : Type} [CommRing B] [CommRing B'] {j : Zp2 p →+* B}
    {j' : Zp2 p →+* B'} (φ : B →+* B') (D : GradedCartierModuleData p j)
    (D' : GradedCartierModuleData p j') (f : D.M →+ D'.M)
    (h : IsBaseChangeAlong' φ D D' f) : j' = φ.comp j :=
  h.1

/-- The unconstrained clauses hold for the identity from `seqData j₁` to
`seqData j₂`, whatever the two coefficient maps are. -/
private theorem unconstrainedBaseChange_seqData
    (j₁ j₂ : Zp2 p →+* GaloisField p 2) :
    UnconstrainedBaseChange (RingHom.id _) (seqData j₁) (seqData j₂)
      (AddMonoidHom.id _) := by
  refine ⟨fun w x => ?_, fun _ => rfl, fun _ => rfl, fun _ => rfl,
    fun _ _ hx => hx, seqBasis j₁, seqData_isHomogeneousVBasis j₁,
    seqData_isHomogeneousVBasis j₂⟩
  rw [WittVector.map_id]
  rfl

/-- The constraint holds: the identity of `seqData j` is a base change along
the identity. -/
example (j : Zp2 p →+* GaloisField p 2) :
    IsBaseChangeAlong' (RingHom.id _) (seqData j) (seqData j)
      (AddMonoidHom.id _) :=
  ⟨(RingHom.id_comp j).symm, unconstrainedBaseChange_seqData j j⟩

/-- The same base change through `IsBaseChangeAlong`, whose target is
indexed by `(RingHom.id _).comp j`. -/
example (j : Zp2 p →+* GaloisField p 2) :
    IsBaseChangeAlong (RingHom.id _) (seqData j)
      (seqData ((RingHom.id _).comp j)) (AddMonoidHom.id _) :=
  (isBaseChangeAlong'_iff _ _ _ _).mp
    ⟨rfl, unconstrainedBaseChange_seqData j _⟩

private theorem exists_pow_ne_self : ∃ x : GaloisField p 2, x ^ p ≠ x := by
  by_contra! h
  have h1 : FiniteField.frobeniusAlgHom (ZMod p) (GaloisField p 2) = 1 := by
    ext x
    simp only [FiniteField.frobeniusAlgHom_apply, ZMod.card, AlgHom.one_apply]
    exact h x
  have h2 := FiniteField.orderOf_frobeniusAlgHom (ZMod p) (GaloisField p 2)
  rw [h1, orderOf_one, GaloisField.finrank p two_ne_zero] at h2
  exact absurd h2 (by norm_num)

private theorem frobenius_comp_constantCoeff_ne :
    (frobenius (GaloisField p 2) p).comp
        (WittVector.constantCoeff : Zp2 p →+* GaloisField p 2) ≠
      WittVector.constantCoeff := by
  intro h
  obtain ⟨x, hx⟩ := exists_pow_ne_self (p := p)
  have hx' := RingHom.congr_fun h (WittVector.teichmuller p x)
  simp only [RingHom.comp_apply, WittVector.constantCoeff_apply,
    WittVector.teichmuller_coeff_zero, frobenius_def] at hx'
  exact hx hx'

/-- Boundary: twist the target's coefficient map by the Frobenius of the
field with `p ^ 2` elements. The unconstrained clauses still hold for the
identity, but the coefficient-map clause fails, so it is not a base change
along the identity. -/
example :
    UnconstrainedBaseChange (RingHom.id _)
      (seqData (p := p) WittVector.constantCoeff)
      (seqData ((frobenius (GaloisField p 2) p).comp WittVector.constantCoeff))
      (AddMonoidHom.id _) ∧
    ¬ IsBaseChangeAlong' (RingHom.id _)
      (seqData (p := p) WittVector.constantCoeff)
      (seqData ((frobenius (GaloisField p 2) p).comp WittVector.constantCoeff))
      (AddMonoidHom.id _) :=
  ⟨unconstrainedBaseChange_seqData _ _,
    fun h => frobenius_comp_constantCoeff_ne (h.1.trans (RingHom.id_comp _))⟩

end SeqExample

end CerednikDrinfeld
