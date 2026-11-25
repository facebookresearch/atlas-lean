/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Group
import Mathlib.Tactic.Positivity

/-!
# Quotients by torsion of finitely presented groups (Kourovka Notebook Problem 19.24)

Kourovka Notebook, Archive of Solved Problems, Problem 19.24 (M. Chiodo, R. Vyas): for a group `G`
let `Tor(G)` be the normal closure of the torsion elements. Does there exist a finitely presented
group `G` such that `G / Tor(G)` is not finitely presented?

This file proves `existsFinitelyPresentedTorsionQuotientNotFinitelyPresented_holds`: such a group
exists.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.24 (M.
Chiodo, R. Vyas). UnsolvedMath record UM-00701572 (`KOU-19.24`), dataset ulamai/UnsolvedMath v1.8.0.

Finite presentability is Mathlib's `Group.IsFinitelyPresented`; `G : Type`.

## Proof

The argument follows the idea of Leary and Minasyan's Construction 3.1 (arXiv:2112.14546): killing
a central element that has roots of all orders `2 ^ k` turns these roots into torsion elements of
unbounded order. Abels' group, whose finite presentability is a deep theorem, is replaced by a
group `G` with five generators `α, β, a, g, f`, modelled on the matrices `diag(1, 2, 1, 1)`,
`diag(1, 1, 2, 1)`, `1 + E₁₂`, `1 + E₂₃` and `1 + E₃₄`. With `c = ⁅a, g⁆` and `b = ⁅g, f⁆`, its
twelve relators say that `α` commutes with `β`, `f` and `c`; `β` commutes with `a` and `b`;
`α * β` commutes with `g`; `a` commutes with `f`; `c` commutes with `a` and `b`; `b` commutes with
`g`; `β⁻¹ * c * β = c ^ 2`; and `⁅c, f⁆ = 1`. All but the last hold for the matrices.

* A commutator computation, using only the relators, shows that `c_k = β ^ k * c * (β ^ k)⁻¹`
  commutes with `⁅c_k, f⁆`, so `⁅c_k, f⁆ ^ (2 ^ k) = ⁅c, f⁆ = 1`: the elements `h_k = ⁅c_k, f⁆`
  are torsion.
* `G` maps to the group of unitriangular `4 × 4` matrices over `ℚ` whose corner entry is read in
  `ℚ / ℤ`, extended by the diagonal matrices `diag(1, 2 ^ i, 2 ^ j, 1)`; there the last relator
  holds as well. Every torsion element of this group is a central corner matrix, and `h_k` maps to
  the corner matrix with entry `1 / 2 ^ k`, of order `2 ^ k`.
* If `G / Tor(G)` were finitely presented, `Tor(G)` would be the normal closure of finitely many
  elements, since `G` is finitely generated. Their images are central corner matrices generating a
  subgroup of bounded exponent, which cannot contain the images of all the `h_k`.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24Wanted

/-- **Torsion closure.** For a group $G$, $\mathrm{Tor}(G)$ is the normal closure in $G$ of the set
of elements of finite order of $G$. -/
abbrev torsionClosure (G : Type*) [Group G] : Subgroup G :=
  Subgroup.normalClosure {g : G | IsOfFinOrder g}

/-- **Kourovka Problem 19.24 (torsion quotients of finitely presented groups).** The statement,
asked by M. Chiodo and R. Vyas, that there exists a finitely presented group $G$ such that
$G / \mathrm{Tor}(G)$ is not finitely presented, where $\mathrm{Tor}(G)$ is the normal closure of
the set of elements of finite order of $G$. -/
def existsFinitelyPresentedTorsionQuotientNotFinitelyPresented : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsFinitelyPresented G ∧
    ¬ Group.IsFinitelyPresented (G ⧸ torsionClosure G)

open scoped commutatorElement
open SemidirectProduct

/-! ### A commutator computation -/

/-- Conjugation by `u` fixes `y` when `u` and `y` commute. -/
private theorem inv_mul_mul_eq_of_commute {H : Type*} [Group H] {u y : H} (h : Commute u y) :
    u⁻¹ * y * u = y := by
  rw [mul_assoc, ← h.eq]; group

/-- If `x` commutes with `w` and with `⁅x, y⁆`, `y` commutes with `⁅y, w⁆`, and `⁅x, y⁆` commutes
with `⁅y, w⁆` (relations of the generators `1 + E₁₂`, `1 + E₂₃` and `1 + E₃₄` of the unitriangular
group), then `⁅x, y⁆` commutes with `⁅⁅x, y⁆, w⁆`. -/
private theorem commute_commutator_commutator {H : Type*} [Group H] (x y w : H)
    (H1 : Commute x w) (H2 : Commute ⁅x, y⁆ x) (H3 : Commute ⁅y, w⁆ y)
    (H4 : Commute ⁅x, y⁆ ⁅y, w⁆) : Commute ⁅x, y⁆ ⁅⁅x, y⁆, w⁆ := by
  set c := ⁅x, y⁆ with hc
  set b := ⁅y, w⁆ with hb
  set h := ⁅c, w⁆ with hh
  have hxw : x * w * x⁻¹ = w := by rw [H1.eq]; group
  have hwx : w * x * w⁻¹ = x := by rw [← H1.eq]; group
  have hxy : x * y * x⁻¹ = c * y := by rw [hc, commutatorElement_def]; group
  have s1 : x * b * x⁻¹ = b * h := by
    have e1 : x * b * x⁻¹ =
        (x * y * x⁻¹) * (x * w * x⁻¹) * (x * y * x⁻¹)⁻¹ * (x * w * x⁻¹)⁻¹ := by
      rw [hb, commutatorElement_def]; group
    have e2 : c * y * w * (c * y)⁻¹ * w⁻¹ = c * b * c⁻¹ * h := by
      rw [hb, hh, commutatorElement_def, commutatorElement_def]; group
    rw [e1, hxw, hxy, e2, H4.eq]; group
  have s2 : Commute x h := by
    rw [hh, commutatorElement_def]
    exact ((H2.symm.mul_right H1).mul_right H2.symm.inv_right).mul_right H1.inv_right
  have s3 : w * y * w⁻¹ = y * b⁻¹ := by
    calc w * y * w⁻¹ = b⁻¹ * y := by rw [hb, commutatorElement_def]; group
      _ = y * b⁻¹ := H3.inv_left.eq
  have s4 : x * b⁻¹ * x⁻¹ * b = h⁻¹ := by
    have : x * b⁻¹ * x⁻¹ = (x * b * x⁻¹)⁻¹ := by group
    rw [this, s1]; group
  have s5 : w * c * w⁻¹ = c * y * h⁻¹ * y⁻¹ := by
    have e1 : w * c * w⁻¹ =
        (w * x * w⁻¹) * (w * y * w⁻¹) * (w * x * w⁻¹)⁻¹ * (w * y * w⁻¹)⁻¹ := by
      rw [hc, commutatorElement_def]; group
    rw [e1, hwx, s3, ← s4, ← hxy]; group
  have s6 : w * c * w⁻¹ = h⁻¹ * c := by rw [hh, commutatorElement_def]; group
  have s7 : Commute (c * y) h := by
    have e : (c * y) * h⁻¹ * (c * y)⁻¹ = h⁻¹ := by
      have e' : (c * y) * h⁻¹ * (c * y)⁻¹ = (c * y * h⁻¹ * y⁻¹) * c⁻¹ := by group
      rw [e', ← s5, s6]; group
    have hc' : Commute (c * y) h⁻¹ := by
      calc (c * y) * h⁻¹ = ((c * y) * h⁻¹ * (c * y)⁻¹) * (c * y) := by group
        _ = h⁻¹ * (c * y) := by rw [e]
    simpa using hc'.inv_right
  have s8 : Commute y h := by
    rw [← hxy] at s7
    have e : y = x⁻¹ * (x * y * x⁻¹) * x := by group
    rw [e]
    exact (s2.inv_left.mul_left s7).mul_left s2
  have e : c = (c * y) * y⁻¹ := by group
  rw [e]
  exact s7.mul_left s8.inv_left

/-- A commutator is multiplicative in its first argument when that argument commutes with it. -/
private theorem commutator_pow_left {H : Type*} [Group H] (x f : H) (hx : Commute x ⁅x, f⁆) :
    ∀ n : ℕ, ⁅x ^ n, f⁆ = ⁅x, f⁆ ^ n
  | 0 => by simp
  | n + 1 => by
    have e : ⁅x ^ (n + 1), f⁆ = x * ⁅x ^ n, f⁆ * x⁻¹ * ⁅x, f⁆ := by
      rw [pow_succ', commutatorElement_def, commutatorElement_def, commutatorElement_def]; group
    rw [e, commutator_pow_left x f hx n, (hx.pow_right n).eq, pow_succ]; group

/-- If `β⁻¹ * c * β = c ^ 2`, the conjugate `β ^ k * c * (β ^ k)⁻¹` is a `2 ^ k`-th root of
`c`. -/
private theorem conj_pow_two_pow {H : Type*} [Group H] (β c : H) (r8 : β⁻¹ * c * β = c ^ 2) :
    ∀ k : ℕ, (β ^ k * c * (β ^ k)⁻¹) ^ (2 ^ k) = c
  | 0 => by simp
  | k + 1 => by
    have e : (β ^ (k + 1) * c * (β ^ (k + 1))⁻¹) ^ 2 = β ^ k * c * (β ^ k)⁻¹ := by
      rw [← MulAut.conj_apply, ← map_pow, ← r8, MulAut.conj_apply, pow_succ]; group
    rw [show 2 ^ (k + 1) = 2 * 2 ^ k by ring, pow_mul, e]
    exact conj_pow_two_pow β c r8 k

/-- The relations of the presented group force
`⁅β ^ k * c * (β ^ k)⁻¹, f⁆ ^ (2 ^ k) = ⁅c, f⁆`, where `c = ⁅a, g⁆`. -/
private theorem commutator_conj_pow_two_pow {H : Type*} [Group H] (α β a g f : H)
    (r1 : Commute α β) (r2 : Commute (α * β) g) (r3 : Commute β a) (r4 : Commute α f)
    (r5 : Commute a f) (r6 : Commute ⁅a, g⁆ a) (r7 : Commute α ⁅a, g⁆)
    (r8 : β⁻¹ * ⁅a, g⁆ * β = ⁅a, g⁆ ^ 2) (r9 : Commute ⁅g, f⁆ g) (r10 : Commute β ⁅g, f⁆)
    (r11 : Commute ⁅a, g⁆ ⁅g, f⁆) (k : ℕ) :
    ⁅β ^ k * ⁅a, g⁆ * (β ^ k)⁻¹, f⁆ ^ (2 ^ k) = ⁅⁅a, g⁆, f⁆ := by
  set B := MulAut.conj (β ^ k) with hB
  set A := MulAut.conj ((α ^ k)⁻¹) with hA
  have hBapp : ∀ y, B y = β ^ k * y * (β ^ k)⁻¹ := fun y => rfl
  have hAapp : ∀ y, A y = (α ^ k)⁻¹ * y * α ^ k := fun y => by
    rw [hA, MulAut.conj_apply, inv_inv]
  have hBa : B a = a := by rw [hBapp, (r3.pow_left k).eq]; group
  have hAf : A f = f := by rw [hAapp, inv_mul_mul_eq_of_commute (r4.pow_left k)]
  have hBb : B ⁅g, f⁆ = ⁅g, f⁆ := by rw [hBapp, (r10.pow_left k).eq]; group
  have hAg : A g = B g := by
    have h := (r2.pow_left k).eq
    rw [r1.mul_pow] at h
    rw [hAapp, hBapp]
    calc (α ^ k)⁻¹ * g * α ^ k
        = (α ^ k)⁻¹ * (α ^ k * β ^ k * g) * (β ^ k)⁻¹ * (α ^ k)⁻¹ * α ^ k := by
          rw [h]; group
      _ = β ^ k * g * (β ^ k)⁻¹ := by group
  have hAc : ∀ y, Commute α y → A y = y := fun y hy => by
    rw [hAapp, inv_mul_mul_eq_of_commute (hy.pow_left k)]
  set gk := B g with hgk
  set ck := B ⁅a, g⁆ with hck
  have hck' : ck = ⁅a, gk⁆ := by rw [hck, map_commutatorElement, hBa]
  have hbk : A ⁅g, f⁆ = ⁅gk, f⁆ := by rw [map_commutatorElement, hAg, hAf]
  have H2 : Commute ⁅a, gk⁆ a := by
    have h := r6.map B
    rw [hBa, ← hck, hck'] at h
    exact h
  have H3 : Commute ⁅gk, f⁆ gk := by rw [← hbk, ← hAg]; exact r9.map A
  have hAck : A ck = ck := by
    apply hAc
    rw [hck, hBapp]
    exact ((r1.pow_right k).mul_right r7).mul_right (r1.pow_right k).inv_right
  have H4 : Commute ⁅a, gk⁆ ⁅gk, f⁆ := by
    rw [← hck', ← hbk, ← hAck, hck, ← hBb]
    exact (r11.map B).map A
  have hcomm : Commute ck ⁅ck, f⁆ := by
    rw [hck']; exact commute_commutator_commutator a gk f r5 H2 H3 H4
  have hpow : ck ^ (2 ^ k) = ⁅a, g⁆ := by
    rw [hck, hBapp]; exact conj_pow_two_pow β ⁅a, g⁆ r8 k
  rw [← hBapp, ← hck, ← commutator_pow_left ck f hcomm, hpow]

/-! ### Finitely presented quotients of finitely generated groups -/

/-- If `G` is finitely generated and `G ⧸ N` is finitely presented, then `N` is the normal closure
of a finite set. -/
private theorem isFinitelyNormallyGenerated_of_isFinitelyPresented_quotient {G : Type*} [Group G]
    [hG : Group.FG G] (N : Subgroup G) [N.Normal] [hQ : Group.IsFinitelyPresented (G ⧸ N)] :
    N.IsFinitelyNormallyGenerated := by
  obtain ⟨X, hX, hXfin⟩ := Group.fg_iff.mp hG
  obtain ⟨m, ψ, hψ, R, hRfin, hR⟩ := hQ.out
  have hπ : Function.Surjective (QuotientGroup.mk' N) := QuotientGroup.mk'_surjective N
  let σ : FreeGroup (Fin m) →* G :=
    FreeGroup.lift fun j => Function.surjInv hπ (ψ (FreeGroup.of j))
  have hσ : ∀ w, QuotientGroup.mk' N (σ w) = ψ w := by
    intro w
    have : (QuotientGroup.mk' N).comp σ = ψ := by
      ext j
      simp only [MonoidHom.coe_comp, Function.comp_apply, σ, FreeGroup.lift_apply_of]
      exact Function.surjInv_eq hπ _
    exact DFunLike.congr_fun this w
  let τ : G → FreeGroup (Fin m) := fun x => Function.surjInv hψ (QuotientGroup.mk' N x)
  have hτ : ∀ x, ψ (τ x) = QuotientGroup.mk' N x := fun x => Function.surjInv_eq hψ _
  let T : Set G := σ '' R ∪ (fun x => x⁻¹ * σ (τ x)) '' X
  refine ⟨T, (hRfin.image _).union (hXfin.image _), le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro _ (⟨r, hr, rfl⟩ | ⟨x, -, rfl⟩)
    · rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff]
      have hr' : r ∈ ψ.ker := hR ▸ Subgroup.subset_normalClosure hr
      exact (hσ r).trans hr'
    · rw [SetLike.mem_coe, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv]
      have h1 := hσ (τ x)
      rw [hτ] at h1
      simp only [QuotientGroup.mk'_apply] at h1
      rw [h1, inv_mul_cancel]
  · set M := Subgroup.normalClosure T with hM
    let θt : FreeGroup (Fin m) →* G ⧸ M := (QuotientGroup.mk' M).comp σ
    have hker : ψ.ker ≤ θt.ker := by
      rw [← hR]
      apply Subgroup.normalClosure_le_normal
      intro r hr
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, θt, MonoidHom.coe_comp,
        Function.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.subset_normalClosure (Or.inl ⟨r, hr, rfl⟩)
    let θ : G ⧸ N →* G ⧸ M :=
      ψ.liftOfRightInverse (Function.surjInv hψ) (Function.rightInverse_surjInv hψ) ⟨θt, hker⟩
    have hθ : ∀ w, θ (ψ w) = θt w := fun w =>
      ψ.liftOfRightInverse_comp_apply _ _ ⟨θt, hker⟩ w
    have hcomp : θ.comp (QuotientGroup.mk' N) = QuotientGroup.mk' M := by
      apply MonoidHom.eq_of_eqOn_dense hX
      intro x hx
      simp only [MonoidHom.coe_comp, Function.comp_apply]
      rw [← hτ, hθ]
      simp only [θt, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq_iff_div_mem]
      have hmem : x⁻¹ * σ (τ x) ∈ M := Subgroup.subset_normalClosure (Or.inr ⟨x, hx, rfl⟩)
      have h2 : σ (τ x) / x = x * (x⁻¹ * σ (τ x)) * x⁻¹ := by rw [div_eq_mul_inv]; group
      rw [h2]
      exact Subgroup.normalClosure_normal.conj_mem _ hmem x
    intro g hg
    have h0 : QuotientGroup.mk' N g = 1 := by
      rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff g).mpr hg
    have h1 : QuotientGroup.mk' M g = 1 := by
      rw [← hcomp, MonoidHom.coe_comp, Function.comp_apply, h0, map_one]
    simpa using h1

/-! ### Unitriangular matrices with corner entry in `ℚ / ℤ` -/

/-- The additive group `ℚ / ℤ`. -/
private abbrev QZ : Type := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- A unitriangular `4 × 4` matrix over `ℚ` whose corner entry `x14` is read in `ℚ / ℤ`. -/
@[ext]
private structure UT where
  x12 : ℚ
  x13 : ℚ
  x14 : QZ
  x23 : ℚ
  x24 : ℚ
  x34 : ℚ

namespace UT

/-- The corner entry of a product, beyond the sum of the corner entries. -/
private def coc (u v : UT) : QZ := ((u.x12 * v.x24 + u.x13 * v.x34 : ℚ) : QZ)

private instance instMulUT : Mul UT where
  mul u v := ⟨u.x12 + v.x12, u.x13 + v.x13 + u.x12 * v.x23, u.x14 + v.x14 + coc u v,
    u.x23 + v.x23, u.x24 + v.x24 + u.x23 * v.x34, u.x34 + v.x34⟩

private instance instOneUT : One UT := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩

private instance instInvUT : Inv UT where
  inv u := ⟨-u.x12, -u.x13 + u.x12 * u.x23,
    -u.x14 - ((-u.x12 * u.x24 + (-u.x13 + u.x12 * u.x23) * u.x34 : ℚ) : QZ),
    -u.x23, -u.x24 + u.x23 * u.x34, -u.x34⟩

@[simp] private theorem mul_x12 (u v : UT) : (u * v).x12 = u.x12 + v.x12 := rfl
@[simp] private theorem mul_x13 (u v : UT) : (u * v).x13 = u.x13 + v.x13 + u.x12 * v.x23 := rfl
@[simp] private theorem mul_x14 (u v : UT) : (u * v).x14 = u.x14 + v.x14 + coc u v := rfl
@[simp] private theorem mul_x23 (u v : UT) : (u * v).x23 = u.x23 + v.x23 := rfl
@[simp] private theorem mul_x24 (u v : UT) : (u * v).x24 = u.x24 + v.x24 + u.x23 * v.x34 := rfl
@[simp] private theorem mul_x34 (u v : UT) : (u * v).x34 = u.x34 + v.x34 := rfl
@[simp] private theorem one_x12 : (1 : UT).x12 = 0 := rfl
@[simp] private theorem one_x13 : (1 : UT).x13 = 0 := rfl
@[simp] private theorem one_x14 : (1 : UT).x14 = 0 := rfl
@[simp] private theorem one_x23 : (1 : UT).x23 = 0 := rfl
@[simp] private theorem one_x24 : (1 : UT).x24 = 0 := rfl
@[simp] private theorem one_x34 : (1 : UT).x34 = 0 := rfl
@[simp] private theorem inv_x12 (u : UT) : u⁻¹.x12 = -u.x12 := rfl
@[simp] private theorem inv_x13 (u : UT) : u⁻¹.x13 = -u.x13 + u.x12 * u.x23 := rfl
@[simp] private theorem inv_x14 (u : UT) : u⁻¹.x14 =
    -u.x14 - ((-u.x12 * u.x24 + (-u.x13 + u.x12 * u.x23) * u.x34 : ℚ) : QZ) := rfl
@[simp] private theorem inv_x23 (u : UT) : u⁻¹.x23 = -u.x23 := rfl
@[simp] private theorem inv_x24 (u : UT) : u⁻¹.x24 = -u.x24 + u.x23 * u.x34 := rfl
@[simp] private theorem inv_x34 (u : UT) : u⁻¹.x34 = -u.x34 := rfl

private theorem coc_assoc (u v w : UT) : coc u v + coc (u * v) w = coc v w + coc u (v * w) := by
  simp only [coc, mul_x12, mul_x13, mul_x24, mul_x34, ← QuotientAddGroup.mk_add]
  congr 1; ring

private instance instGroupUT : Group UT := Group.ofLeftAxioms
  (fun u v w => by
    ext
    · simp only [mul_x12]; ring
    · simp only [mul_x12, mul_x13, mul_x23]; ring
    · simp only [mul_x14]
      calc u.x14 + v.x14 + coc u v + w.x14 + coc (u * v) w
          = u.x14 + v.x14 + w.x14 + (coc u v + coc (u * v) w) := by abel
        _ = u.x14 + v.x14 + w.x14 + (coc v w + coc u (v * w)) := by rw [coc_assoc]
        _ = u.x14 + (v.x14 + w.x14 + coc v w) + coc u (v * w) := by abel
    · simp only [mul_x23]; ring
    · simp only [mul_x23, mul_x24, mul_x34]; ring
    · simp only [mul_x34]; ring)
  (fun u => by ext <;> simp [coc])
  (fun u => by
    ext
    · simp
    · simp
    · simp only [mul_x14, inv_x14, coc, inv_x12, inv_x13, one_x14]; abel
    · simp
    · simp
    · simp)

/-- Conjugation by the diagonal matrix `diag(1, s, t, 1)`. -/
private def scale (s t : ℚ) (u : UT) : UT :=
  ⟨s⁻¹ * u.x12, t⁻¹ * u.x13, u.x14, s * t⁻¹ * u.x23, s * u.x24, t * u.x34⟩

private theorem scale_mul {s t : ℚ} (hs : s ≠ 0) (ht : t ≠ 0) (u v : UT) :
    scale s t (u * v) = scale s t u * scale s t v := by
  ext <;> simp only [scale, mul_x12, mul_x13, mul_x14, mul_x23, mul_x24, mul_x34]
  · ring
  · field_simp
  · simp only [coc]; congr 2; field_simp
  · ring
  · field_simp
  · ring

private theorem scale_scale (s t s' t' : ℚ) (u : UT) :
    scale s t (scale s' t' u) = scale (s * s') (t * t') u := by
  ext <;> simp only [scale] <;> ring

private theorem scale_one (u : UT) : scale 1 1 u = u := by
  ext <;> simp [scale]

/-- Conjugation by `diag(1, 2 ^ i, 2 ^ j, 1)`. -/
private def scaleAut (i j : ℤ) : MulAut UT where
  toFun := scale ((2 : ℚ) ^ i) ((2 : ℚ) ^ j)
  invFun := scale ((2 : ℚ) ^ (-i)) ((2 : ℚ) ^ (-j))
  left_inv u := by
    simp only [scale_scale, ← zpow_add₀ (two_ne_zero (α := ℚ)), neg_add_cancel, zpow_zero,
      scale_one]
  right_inv u := by
    simp only [scale_scale, ← zpow_add₀ (two_ne_zero (α := ℚ)), add_neg_cancel, zpow_zero,
      scale_one]
  map_mul' u v := scale_mul (zpow_ne_zero _ two_ne_zero) (zpow_ne_zero _ two_ne_zero) u v

private theorem scaleAut_apply (i j : ℤ) (u : UT) :
    scaleAut i j u = scale ((2 : ℚ) ^ i) ((2 : ℚ) ^ j) u := rfl

/-- The action of `ℤ²` on `UT` by the diagonal matrices `diag(1, 2 ^ i, 2 ^ j, 1)`. -/
private def act : Multiplicative (ℤ × ℤ) →* MulAut UT where
  toFun d := scaleAut d.toAdd.1 d.toAdd.2
  map_one' := by
    ext u : 1
    simp only [toAdd_one, Prod.fst_zero, Prod.snd_zero, scaleAut_apply, zpow_zero, scale_one,
      MulAut.one_apply]
  map_mul' d d' := by
    ext u : 1
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, scaleAut_apply, MulAut.mul_apply,
      scale_scale, zpow_add₀ (two_ne_zero (α := ℚ))]

private theorem act_apply (d : Multiplicative (ℤ × ℤ)) (u : UT) :
    act d u = scale ((2 : ℚ) ^ d.toAdd.1) ((2 : ℚ) ^ d.toAdd.2) u := rfl

/-- The elementary matrix `1 + E₁₂`. -/
private def e12 : UT := ⟨1, 0, 0, 0, 0, 0⟩
/-- The elementary matrix `1 + E₂₃`. -/
private def e23 : UT := ⟨0, 0, 0, 1, 0, 0⟩
/-- The elementary matrix `1 + E₃₄`. -/
private def e34 : UT := ⟨0, 0, 0, 0, 0, 1⟩
/-- The matrix `1 + r E₁₃`. -/
private def e13 (r : ℚ) : UT := ⟨0, r, 0, 0, 0, 0⟩
/-- The elementary matrix `1 + E₂₄`. -/
private def e24 : UT := ⟨0, 0, 0, 0, 1, 0⟩
/-- The central matrix with corner entry `q`. -/
private def e14 (q : QZ) : UT := ⟨0, 0, q, 0, 0, 0⟩

private theorem comm_e12_e23 : ⁅e12, e23⁆ = e13 1 := by
  ext <;> simp [commutatorElement_def, e12, e23, e13, coc]

private theorem comm_e23_e34 : ⁅e23, e34⁆ = e24 := by
  ext <;> simp [commutatorElement_def, e23, e34, e24, coc]

private theorem comm_e13_e34 (r : ℚ) : ⁅e13 r, e34⁆ = e14 (r : QZ) := by
  ext <;> simp [commutatorElement_def, e13, e34, e14, coc]

private theorem commute_e14 (q : QZ) (u : UT) : Commute (e14 q) u := by
  ext <;> simp [e14, coc, add_comm]

private theorem commute_e12_e34 : Commute e12 e34 := by
  ext <;> simp [e12, e34, coc]

private theorem commute_e13_e12 : Commute (e13 1) e12 := by
  ext <;> simp [e12, e13, coc]

private theorem commute_e24_e23 : Commute e24 e23 := by
  ext <;> simp [e24, e23, coc]

private theorem commute_e13_e24 : Commute (e13 1) e24 := by
  ext <;> simp [e13, e24, coc]

private theorem e13_sq : e13 1 ^ 2 = e13 2 := by
  rw [pow_two]; ext <;> simp [e13, coc]; norm_num

private theorem e14_one : e14 ((1 : ℚ) : QZ) = 1 := by
  ext <;> simp [e14]

private theorem e14_mul (q q' : QZ) : e14 q * e14 q' = e14 (q + q') := by
  ext <;> simp [e14, coc]

private theorem e14_zero : e14 0 = 1 := by ext <;> simp [e14]

private theorem e14_inv (q : QZ) : (e14 q)⁻¹ = e14 (-q) := by
  ext <;> simp [e14]

private theorem e14_injective : Function.Injective e14 := fun _ _ h => congrArg UT.x14 h

private theorem act_e14 (d : Multiplicative (ℤ × ℤ)) (q : QZ) : act d (e14 q) = e14 q := by
  ext <;> simp [act_apply, scale, e14]

private theorem pow_x12 (u : UT) (n : ℕ) : (u ^ n).x12 = n * u.x12 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_x12, ih]; push_cast; ring

private theorem pow_x23 (u : UT) (n : ℕ) : (u ^ n).x23 = n * u.x23 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_x23, ih]; push_cast; ring

private theorem pow_x34 (u : UT) (n : ℕ) : (u ^ n).x34 = n * u.x34 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_x34, ih]; push_cast; ring

private theorem pow_x13 (u : UT) (h23 : u.x23 = 0) (n : ℕ) : (u ^ n).x13 = n * u.x13 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_x13, ih, h23]; push_cast; ring

private theorem pow_x24 (u : UT) (h34 : u.x34 = 0) (n : ℕ) : (u ^ n).x24 = n * u.x24 := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, mul_x24, ih, h34]; push_cast; ring

/-- Every torsion element of `UT` is central, with only its corner entry nonzero. -/
private theorem eq_e14_of_pow_eq_one (u : UT) {n : ℕ} (hn : 0 < n) (h : u ^ n = 1) :
    u = e14 u.x14 := by
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  have key : ∀ x : ℚ, (n : ℚ) * x = 0 → x = 0 := fun x hx =>
    (mul_eq_zero.mp hx).resolve_left hn'
  have h12 := key _ (by rw [← pow_x12, h, one_x12])
  have h23 := key _ (by rw [← pow_x23, h, one_x23])
  have h34 := key _ (by rw [← pow_x34, h, one_x34])
  have h13 := key _ (by rw [← pow_x13 u h23, h, one_x13])
  have h24 := key _ (by rw [← pow_x24 u h34, h, one_x24])
  ext <;> simp [e14, h12, h23, h34, h13, h24]

end UT

/-- The group `UT ⋊ ℤ²`, with `ℤ²` acting by the diagonal matrices `diag(1, 2 ^ i, 2 ^ j, 1)`. -/
private abbrev Target : Type := UT ⋊[UT.act] Multiplicative (ℤ × ℤ)

/-- The image of `α`: the diagonal matrix `diag(1, 2, 1, 1)`. -/
private def imgα : Target := inr (Multiplicative.ofAdd ((1 : ℤ), (0 : ℤ)))

/-- The image of `β`: the diagonal matrix `diag(1, 1, 2, 1)`. -/
private def imgβ : Target := inr (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))

private theorem conj_inr (d : Multiplicative (ℤ × ℤ)) (u : UT) :
    (inr d : Target) * inl u * (inr d)⁻¹ = inl (UT.act d u) := by
  rw [inl_aut, map_inv]

private theorem commute_inr_inl {d : Multiplicative (ℤ × ℤ)} {u : UT} (h : UT.act d u = u) :
    Commute (inr d : Target) (inl u) := by
  have e := conj_inr d u
  rw [h] at e
  calc (inr d : Target) * inl u = ((inr d : Target) * inl u * (inr d)⁻¹) * inr d := by group
    _ = inl u * inr d := by rw [e]

private theorem commute_inl_e14 (q : QZ) (t : Target) : Commute (inl (UT.e14 q)) t := by
  rw [← inl_left_mul_inr_right t]
  exact ((UT.commute_e14 q t.left).map inl).mul_right
    (commute_inr_inl (UT.act_e14 t.right q)).symm

/-- Every torsion element of `Target` is a central corner matrix. -/
private theorem eq_inl_e14_of_pow_eq_one (t : Target) {n : ℕ} (hn : 0 < n) (h : t ^ n = 1) :
    t = inl (UT.e14 t.left.x14) := by
  have hr : t.right ^ n = 1 := by
    have := congrArg (rightHom : Target →* _) h
    rwa [map_pow, map_one, rightHom_eq_right] at this
  have hr1 : t.right = 1 := by
    have h2 : n • t.right.toAdd = 0 := by rw [← toAdd_pow, hr]; rfl
    have hn' : (n : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
    have h3 : t.right.toAdd = 0 := by
      ext
      · have := congrArg Prod.fst h2
        simp only [Prod.fst_zero, nsmul_eq_mul] at this
        exact (mul_eq_zero.mp this).resolve_left hn'
      · have := congrArg Prod.snd h2
        simp only [Prod.snd_zero, nsmul_eq_mul] at this
        exact (mul_eq_zero.mp this).resolve_left hn'
    exact h3
  have ht : t = inl t.left := by
    conv_lhs => rw [← inl_left_mul_inr_right t, hr1, map_one, mul_one]
  have hl : t.left ^ n = 1 := by
    rw [ht, ← map_pow] at h
    exact inl_injective (h.trans (map_one inl).symm)
  rw [ht, left_inl, ← UT.eq_e14_of_pow_eq_one t.left hn hl]

/-- The central corner matrices whose entry is killed by `m`. -/
private def cornerSubgroup (m : ℕ) : Subgroup Target where
  carrier := {t | ∃ q : QZ, t = inl (UT.e14 q) ∧ m • q = 0}
  mul_mem' := by
    rintro _ _ ⟨q, rfl, hq⟩ ⟨q', rfl, hq'⟩
    exact ⟨q + q', by rw [← map_mul, UT.e14_mul], by rw [nsmul_add, hq, hq', add_zero]⟩
  one_mem' := ⟨0, by rw [UT.e14_zero, map_one], nsmul_zero m⟩
  inv_mem' := by
    rintro _ ⟨q, rfl, hq⟩
    exact ⟨-q, by rw [← map_inv, UT.e14_inv], by rw [smul_neg, hq, neg_zero]⟩

private instance cornerSubgroup_normal (m : ℕ) : (cornerSubgroup m).Normal where
  conj_mem := by
    rintro _ ⟨q, rfl, hq⟩ g
    refine ⟨q, ?_, hq⟩
    rw [(commute_inl_e14 q g).symm.eq]; group

private theorem qz_isOfFinAddOrder (q : QZ) : IsOfFinAddOrder q := by
  induction q using QuotientAddGroup.induction_on with
  | H r =>
    rw [isOfFinAddOrder_iff_nsmul_eq_zero]
    refine ⟨r.den, r.den_pos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_zmultiples_iff]
    exact ⟨r.num, by rw [zsmul_one, nsmul_eq_mul, mul_comm, Rat.mul_den_eq_num]⟩

/-! ### The finitely presented group -/

local notation "Xα" => FreeGroup.of (0 : Fin 5)
local notation "Xβ" => FreeGroup.of (1 : Fin 5)
local notation "Xa" => FreeGroup.of (2 : Fin 5)
local notation "Xg" => FreeGroup.of (3 : Fin 5)
local notation "Xf" => FreeGroup.of (4 : Fin 5)

/-- The twelve relators. -/
private def rels : Set (FreeGroup (Fin 5)) :=
  {⁅Xα, Xβ⁆, ⁅Xα * Xβ, Xg⁆, ⁅Xβ, Xa⁆, ⁅Xα, Xf⁆, ⁅Xa, Xf⁆, ⁅⁅Xa, Xg⁆, Xa⁆, ⁅Xα, ⁅Xa, Xg⁆⁆,
    Xβ⁻¹ * ⁅Xa, Xg⁆ * Xβ * (⁅Xa, Xg⁆ ^ 2)⁻¹, ⁅⁅Xg, Xf⁆, Xg⁆, ⁅Xβ, ⁅Xg, Xf⁆⁆,
    ⁅⁅Xa, Xg⁆, ⁅Xg, Xf⁆⁆, ⁅⁅Xa, Xg⁆, Xf⁆}

private instance finite_rels : Finite rels := by unfold rels; infer_instance

/-- The finitely presented group of the construction. -/
private abbrev PG : Type := PresentedGroup rels

local notation "gα" => (PresentedGroup.of (0 : Fin 5) : PG)
local notation "gβ" => (PresentedGroup.of (1 : Fin 5) : PG)
local notation "ga" => (PresentedGroup.of (2 : Fin 5) : PG)
local notation "gg" => (PresentedGroup.of (3 : Fin 5) : PG)
local notation "gf" => (PresentedGroup.of (4 : Fin 5) : PG)

private theorem mk_of (i : Fin 5) :
    PresentedGroup.mk rels (FreeGroup.of i) = PresentedGroup.of i := rfl

private theorem rel_eq_one {r : FreeGroup (Fin 5)} (hr : r ∈ rels) :
    PresentedGroup.mk rels r = 1 :=
  PresentedGroup.one_of_mem hr

private theorem commute_of_mem_rels {x y : FreeGroup (Fin 5)} (hr : ⁅x, y⁆ ∈ rels) :
    Commute (PresentedGroup.mk rels x) (PresentedGroup.mk rels y) := by
  rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
  exact rel_eq_one hr

/-- The element `h_k = ⁅β ^ k * ⁅a, g⁆ * (β ^ k)⁻¹, f⁆`. -/
private def hk (k : ℕ) : PG := ⁅gβ ^ k * ⁅ga, gg⁆ * (gβ ^ k)⁻¹, gf⁆

private theorem hk_pow (k : ℕ) : hk k ^ (2 ^ k) = 1 := by
  have r1 : Commute gα gβ := commute_of_mem_rels (x := Xα) (y := Xβ) (by simp [rels])
  have r2 : Commute (gα * gβ) gg := by
    have := commute_of_mem_rels (x := Xα * Xβ) (y := Xg) (by simp [rels])
    rwa [map_mul] at this
  have r3 : Commute gβ ga := commute_of_mem_rels (x := Xβ) (y := Xa) (by simp [rels])
  have r4 : Commute gα gf := commute_of_mem_rels (x := Xα) (y := Xf) (by simp [rels])
  have r5 : Commute ga gf := commute_of_mem_rels (x := Xa) (y := Xf) (by simp [rels])
  have r6 : Commute ⁅ga, gg⁆ ga := by
    have := commute_of_mem_rels (x := ⁅Xa, Xg⁆) (y := Xa) (by simp [rels])
    rwa [map_commutatorElement] at this
  have r7 : Commute gα ⁅ga, gg⁆ := by
    have := commute_of_mem_rels (x := Xα) (y := ⁅Xa, Xg⁆) (by simp [rels])
    rwa [map_commutatorElement] at this
  have r8 : gβ⁻¹ * ⁅ga, gg⁆ * gβ = ⁅ga, gg⁆ ^ 2 := by
    have := rel_eq_one (r := Xβ⁻¹ * ⁅Xa, Xg⁆ * Xβ * (⁅Xa, Xg⁆ ^ 2)⁻¹) (by simp [rels])
    simp only [map_mul, map_inv, map_pow, map_commutatorElement, mk_of] at this
    exact mul_inv_eq_one.mp this
  have r9 : Commute ⁅gg, gf⁆ gg := by
    have := commute_of_mem_rels (x := ⁅Xg, Xf⁆) (y := Xg) (by simp [rels])
    rwa [map_commutatorElement] at this
  have r10 : Commute gβ ⁅gg, gf⁆ := by
    have := commute_of_mem_rels (x := Xβ) (y := ⁅Xg, Xf⁆) (by simp [rels])
    rwa [map_commutatorElement] at this
  have r11 : Commute ⁅ga, gg⁆ ⁅gg, gf⁆ := by
    have := commute_of_mem_rels (x := ⁅Xa, Xg⁆) (y := ⁅Xg, Xf⁆) (by simp [rels])
    rwa [map_commutatorElement, map_commutatorElement] at this
  have r12 : ⁅⁅ga, gg⁆, gf⁆ = 1 := by
    have := rel_eq_one (r := ⁅⁅Xa, Xg⁆, Xf⁆) (by simp [rels])
    simpa only [map_commutatorElement, mk_of] using this
  rw [hk, commutator_conj_pow_two_pow gα gβ ga gg gf r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 k, r12]

/-- The images of the five generators in `Target`. -/
private def img : Fin 5 → Target := ![imgα, imgβ, inl UT.e12, inl UT.e23, inl UT.e34]

private theorem img_0 : img 0 = imgα := rfl
private theorem img_1 : img 1 = imgβ := rfl
private theorem img_2 : img 2 = inl UT.e12 := rfl
private theorem img_3 : img 3 = inl UT.e23 := rfl
private theorem img_4 : img 4 = inl UT.e34 := rfl

private theorem lift_rels : ∀ r ∈ rels, FreeGroup.lift img r = 1 := by
  intro r hr
  simp only [rels, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [map_commutatorElement, map_mul, map_inv, map_pow, FreeGroup.lift_apply_of,
      img_0, img_1, img_2, img_3, img_4]
  · rw [commutatorElement_eq_one_iff_commute]; exact (Commute.all _ _).map inr
  · rw [commutatorElement_eq_one_iff_commute, imgα, imgβ, ← map_mul]
    apply commute_inr_inl
    ext <;> simp [UT.act_apply, UT.scale, UT.e23]
  · rw [commutatorElement_eq_one_iff_commute, imgβ]
    apply commute_inr_inl
    ext <;> simp [UT.act_apply, UT.scale, UT.e12]
  · rw [commutatorElement_eq_one_iff_commute, imgα]
    apply commute_inr_inl
    ext <;> simp [UT.act_apply, UT.scale, UT.e34]
  · rw [← map_commutatorElement, commutatorElement_eq_one_iff_commute.mpr UT.commute_e12_e34,
      map_one]
  · rw [← map_commutatorElement, ← map_commutatorElement, UT.comm_e12_e23,
      commutatorElement_eq_one_iff_commute.mpr UT.commute_e13_e12, map_one]
  · rw [← map_commutatorElement, UT.comm_e12_e23, commutatorElement_eq_one_iff_commute, imgα]
    apply commute_inr_inl
    ext <;> simp [UT.act_apply, UT.scale, UT.e13]
  · rw [← map_commutatorElement, UT.comm_e12_e23, ← map_pow, UT.e13_sq, mul_inv_eq_one]
    have e : imgβ⁻¹ * inl (UT.e13 1) * imgβ =
        inl (UT.act (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)))⁻¹ (UT.e13 1)) := by
      rw [imgβ, ← conj_inr, map_inv, inv_inv]
    rw [e]
    congr 1
    rw [UT.act_apply]
    ext <;> simp [UT.scale, UT.e13]
  · rw [← map_commutatorElement, ← map_commutatorElement, UT.comm_e23_e34,
      commutatorElement_eq_one_iff_commute.mpr UT.commute_e24_e23, map_one]
  · rw [← map_commutatorElement, UT.comm_e23_e34, commutatorElement_eq_one_iff_commute, imgβ]
    apply commute_inr_inl
    ext <;> simp [UT.act_apply, UT.scale, UT.e24]
  · rw [← map_commutatorElement, ← map_commutatorElement, ← map_commutatorElement,
      UT.comm_e12_e23, UT.comm_e23_e34,
      commutatorElement_eq_one_iff_commute.mpr UT.commute_e13_e24, map_one]
  · rw [← map_commutatorElement, ← map_commutatorElement, UT.comm_e12_e23, UT.comm_e13_e34,
      UT.e14_one, map_one]

/-- The homomorphism from the presented group to `Target`. -/
private def toTarget : PG →* Target := PresentedGroup.toGroup lift_rels

private theorem toTarget_of (i : Fin 5) : toTarget (PresentedGroup.of i) = img i :=
  PresentedGroup.toGroup.of lift_rels

private theorem toTarget_hk (k : ℕ) :
    toTarget (hk k) = inl (UT.e14 ((((2 : ℚ) ^ k)⁻¹ : ℚ) : QZ)) := by
  simp only [hk, map_commutatorElement, map_mul, map_inv, map_pow, toTarget_of, img_1, img_2,
    img_3, img_4]
  rw [← map_commutatorElement, UT.comm_e12_e23, imgβ, ← map_pow, conj_inr,
    ← map_commutatorElement]
  have e : UT.act (Multiplicative.ofAdd ((0 : ℤ), (1 : ℤ)) ^ k) (UT.e13 1) =
      UT.e13 (((2 : ℚ) ^ k)⁻¹) := by
    rw [UT.act_apply]
    ext <;> simp [UT.scale, UT.e13, toAdd_pow]
  rw [e, UT.comm_e13_e34]

private theorem not_isFinitelyPresented_quotient :
    ¬ Group.IsFinitelyPresented (PG ⧸ torsionClosure PG) := by
  intro hfp
  have : Group.FG PG := Group.fg_of_surjective (PresentedGroup.mk_surjective rels)
  obtain ⟨S, hSfin, hS⟩ :=
    isFinitelyNormallyGenerated_of_isFinitelyPresented_quotient (torsionClosure PG)
  have h0 : torsionClosure PG ≤ (cornerSubgroup 0).comap toTarget := by
    apply Subgroup.normalClosure_le_normal
    intro g hg
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
    exact ⟨_, eq_inl_e14_of_pow_eq_one (toTarget g) hn (by rw [← map_pow, hgn, map_one]),
      zero_nsmul _⟩
  have hq : ∀ s ∈ S, toTarget s = inl (UT.e14 (toTarget s).left.x14) := by
    intro s hs
    obtain ⟨q, hq, -⟩ := h0 (hS ▸ Subgroup.subset_normalClosure hs)
    rw [hq]
    rfl
  let m : ℕ := ∏ s ∈ hSfin.toFinset, addOrderOf (toTarget s).left.x14
  have hm : 0 < m := Finset.prod_pos fun s _ => (qz_isOfFinAddOrder _).addOrderOf_pos
  have hSm : S ⊆ (cornerSubgroup m).comap toTarget := by
    intro s hs
    refine ⟨_, hq s hs, ?_⟩
    rw [← addOrderOf_dvd_iff_nsmul_eq_zero]
    exact Finset.dvd_prod_of_mem _ (hSfin.mem_toFinset.mpr hs)
  have hle : torsionClosure PG ≤ (cornerSubgroup m).comap toTarget := by
    rw [← hS]; exact Subgroup.normalClosure_le_normal hSm
  have htor : hk m ∈ torsionClosure PG :=
    Subgroup.subset_normalClosure
      (isOfFinOrder_iff_pow_eq_one.mpr ⟨2 ^ m, by positivity, hk_pow m⟩)
  obtain ⟨q, hq', hmq⟩ := hle htor
  rw [toTarget_hk] at hq'
  have hq'' := UT.e14_injective (inl_injective hq')
  rw [← hq'', ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_zmultiples_iff] at hmq
  obtain ⟨z, hz⟩ := hmq
  rw [zsmul_one, nsmul_eq_mul] at hz
  have h1 : (0 : ℚ) < z := by rw [hz]; positivity
  have h2 : (z : ℚ) < 1 := by
    rw [hz, ← div_eq_mul_inv, div_lt_one (by positivity)]
    exact_mod_cast Nat.lt_two_pow_self
  have h1' : (0 : ℤ) < z := by exact_mod_cast h1
  have h2' : z < 1 := by exact_mod_cast h2
  omega

/--
**Torsion quotients of finitely presented groups need not be finitely presented.** There exists
a finitely presented group $G$ such that $G / \mathrm{Tor}(G)$ is not finitely presented, where
$\mathrm{Tor}(G)$ is the normal closure of the set of elements of finite order of $G$.

The Kourovka Archive answers Problem 19.24 "Yes, such groups exist": Leary and Minasyan
(Constructions 3.1 and 3.2) give a soluble example and a virtually torsion-free example.

Source: E. I. Khukhro and V. D.
Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue,
arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 19.24 (M. Chiodo, R. Vyas);
resolution: I. J. Leary and A. Minasyan, A note on torsion length and torsion subgroups, J. Group
Theory 26 (2023), no. 4, 741-750 (arXiv:2112.14546), Section 3, Construction 3.1 (Abels' finitely
presented soluble group H modulo an infinite cyclic central subgroup C: G = H / C has G / Tor(G) ≅ H
/ Z(H), which is not finitely presented) and Construction 3.2 (a virtually torsion-free example
built from Bestvina-Brady groups); Kourovka Archive, Problem 19.24: Yes, such groups exist, one
soluble and one virtually torsion-free, https://arxiv.org/abs/2112.14546.
-/
theorem existsFinitelyPresentedTorsionQuotientNotFinitelyPresented_holds :
    existsFinitelyPresentedTorsionQuotientNotFinitelyPresented :=
  ⟨PG, inferInstance, inferInstance, not_isFinitelyPresented_quotient⟩

end MathlibExt.GroupTheory.TorsionQuotientFinitelyPresentedKourovka19Problem24Wanted
