/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Finiteness
public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Finsupp.Fintype
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Residually finite `p`-groups and torsion-free nilpotence (Kourovka Notebook Problem 14.52)

Kourovka Notebook, Archive of Solved Problems, Problem 14.52 (Yu. V. Kuz'min): a finitely generated
residually torsion-free nilpotent group is residually a finite `p`-group for every prime `p`. Is the
converse true?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 14.52 (Yu. V.
Kuz'min). UnsolvedMath record UM-00701037 (`KOU-14.52`), dataset ulamai/UnsolvedMath v1.8.0.

Residually `𝒫`: every `g ≠ 1` lies outside some normal subgroup `N` with `G / N ∈ 𝒫`. The converse
is stated for finitely generated groups, as in the problem.

We refute the converse by a four-generated group whose finite reductions separate each element
at every prime. Its multiplication uses two copies of the integral group ring of the integers,
with shifts in opposite directions. A pairing of the two copies takes values in a central copy of
the integers. Finite differences of the pairing values give nonzero multiples of the central
generator arbitrarily far down the lower central series.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ResiduallyFinitePGroupTorsionFreeNilpotentKourovka14Problem52Wanted

/-- **Kuz'min's question on residually finite $p$-groups (Kourovka 14.52).** The statement that
every finitely generated group $G$ that is residually a finite $p$-group for every prime $p$ is
residually torsion-free nilpotent. Here $G$ is residually a finite $p$-group when every element
$g \ne 1$ lies outside some normal subgroup $N$ such that $G/N$ is a finite $p$-group, and
residually torsion-free nilpotent when every element $g \ne 1$ lies outside some normal subgroup
$N$ such that $G/N$ is nilpotent and has no nontrivial elements of finite order. -/
def residuallyFinitePImpliesResiduallyTorsionFreeNilpotent : Prop :=
  ∀ (G : Type) [Group G], Group.FG G →
    (∀ p : ℕ, p.Prime → ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), g ∉ N ∧
      Finite (G ⧸ N) ∧ IsPGroup p (G ⧸ N)) →
    ∀ g : G, g ≠ 1 → ∃ (N : Subgroup G) (_ : N.Normal), g ∉ N ∧ Group.IsNilpotent (G ⧸ N) ∧
      ∀ y : G ⧸ N, y ≠ 1 → ¬ IsOfFinOrder y

noncomputable section

open scoped BigOperators commutatorElement
open Polynomial

-- These integer polynomials have expanding sets of consecutive integer roots.
private def falling (m : ℕ) (a i : ℤ) : ℤ := (descPochhammer ℤ m).eval (i + a)

private def term (n : ℕ) (i : ℤ) : ℤ := (n.factorial : ℤ) * falling (2 * n) n i

private def pairingValues (i : ℤ) : ℤ := ∑ n ∈ Finset.range (i.natAbs + 1), term n i

private theorem term_zero {n : ℕ} {i : ℤ} (hl : -(n : ℤ) ≤ i) (hr : i < n) :
    term n i = 0 := by
  have h : 0 ≤ i + (n : ℤ) := by omega
  have hn : (i + (n : ℤ)).toNat < 2 * n := by omega
  have hz := descPochhammer_eval_natCast_of_lt (R := ℤ) hn
  rw [Int.toNat_of_nonneg h] at hz
  simp [term, falling, hz]

private theorem pairingValues_eq_sum {N : ℕ} {i : ℤ} (hi : i.natAbs ≤ N) :
    pairingValues i = ∑ n ∈ Finset.range (N + 1), term n i := by
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hx
  simp only [Finset.mem_range, not_lt] at hn hx
  exact term_zero (by omega) (by omega)

private theorem term_cast_zero {m n : ℕ} (hm : 0 < m) (hmn : m ≤ n) (i : ℤ) :
    (term n i : ZMod m) = 0 := by
  have h := Nat.dvd_factorial hm hmn
  have hz : ((n.factorial : ℤ) : ZMod m) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 (Int.natCast_dvd_natCast.2 h)
  simp only [term, Int.cast_mul, hz, zero_mul]

private theorem pairingValues_cast {m : ℕ} (hm : 0 < m) (i : ℤ) :
    (pairingValues i : ZMod m) = ∑ n ∈ Finset.range m, (term n i : ZMod m) := by
  rw [pairingValues_eq_sum (le_max_left i.natAbs m), Int.cast_sum]
  symm
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro n hn hx
  exact term_cast_zero hm (Nat.le_of_not_gt (by simpa using hx)) i

private theorem pairingValues_cast_eq {m : ℕ} (hm : 0 < m) {i j : ℤ}
    (hij : (i : ZMod m) = (j : ZMod m)) :
    (pairingValues i : ZMod m) = (pairingValues j : ZMod m) := by
  rw [pairingValues_cast hm, pairingValues_cast hm]
  exact Finset.sum_congr rfl fun n _ ↦ by
    simp only [term, falling, Int.cast_mul, descPochhammer_eval_cast, Int.cast_add, hij]

private theorem diff_falling (m : ℕ) (a : ℤ) :
    fwdDiff 1 (falling (m + 1) a) = (m + 1 : ℤ) • falling m a := by
  ext i
  have h := congrArg (Polynomial.eval (i + 1 + a))
    (descPochhammer_succ_comp_X_sub_one ℤ m)
  simp only [eval_comp, eval_sub, eval_X, eval_one, eval_mul, eval_add, eval_natCast,
    smul_eq_mul] at h
  rw [show i + 1 + a - 1 = i + a by ring] at h
  simp only [fwdDiff, falling, Pi.smul_apply, smul_eq_mul]
  omega

private theorem iter_falling_self (m : ℕ) (a : ℤ) :
    (fwdDiff (1 : ℤ))^[m] (falling m a) = fun _ ↦ (m.factorial : ℤ) := by
  induction m with
  | zero => ext i; simp [falling]
  | succ m ih =>
    rw [Function.iterate_succ_apply, diff_falling, fwdDiff_iter_const_smul, ih]
    ext i
    simp [Nat.factorial_succ]

private theorem iter_falling_of_lt {m n : ℕ} (h : m < n) (a : ℤ) :
    (fwdDiff (1 : ℤ))^[n] (falling m a) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt h
  rw [show m + k + 1 = (k + 1) + m by omega, Function.iterate_add_apply, iter_falling_self,
    Function.iterate_succ_apply, fwdDiff_const]
  exact Function.iterate_fixed (show fwdDiff (1 : ℤ) (0 : ℤ → ℤ) = 0 by ext; simp [fwdDiff]) k

private theorem term_eq_smul (n : ℕ) : term n = (n.factorial : ℤ) • falling (2 * n) n := rfl

-- On the interval [-n, n], the 2n-th difference kills every lower-degree summand. The
-- higher summands vanish throughout this interval, leaving the term with index n.
private theorem pairingValues_diff (n : ℕ) :
    (fwdDiff (1 : ℤ))^[2 * n] pairingValues (-(n : ℤ)) =
      (n.factorial : ℤ) * ((2 * n).factorial : ℤ) := by
  let F : ℤ → ℤ := ∑ m ∈ Finset.range (n + 1), term m
  have hlocal : (fwdDiff (1 : ℤ))^[2 * n] pairingValues (-(n : ℤ)) =
      (fwdDiff (1 : ℤ))^[2 * n] F (-(n : ℤ)) := by
    rw [fwdDiff_iter_eq_sum_shift, fwdDiff_iter_eq_sum_shift]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    simp only [Finset.mem_range] at hk
    congr 1
    simp only [F, Finset.sum_apply]
    apply pairingValues_eq_sum
    simp only [nsmul_eq_mul, mul_one]
    omega
  rw [hlocal]
  simp only [F, fwdDiff_iter_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single_of_mem n (Finset.mem_range_succ_iff.mpr le_rfl)]
  · simp only [term_eq_smul, fwdDiff_iter_const_smul, iter_falling_self,
      Pi.smul_apply, smul_eq_mul]
  · intro m hm hmn
    have h : 2 * m < 2 * n := by simp only [Finset.mem_range] at hm; omega
    simp only [term_eq_smul, fwdDiff_iter_const_smul, iter_falling_of_lt h,
      smul_zero, Pi.zero_apply]


section ShiftGroup

variable {R I S J : Type*} [CommRing R] [AddCommGroup I] [CommRing S] [AddCommGroup J]

private def trace (f : I → R) : AddMonoidAlgebra R I →+ R :=
  (Finsupp.liftAddHom fun i ↦ AddMonoidHom.mulRight (f i)).comp
    AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom

omit [AddCommGroup I] in
private theorem trace_single (f : I → R) (i : I) (r : R) :
    trace f (AddMonoidAlgebra.single i r) = r * f i := by
  simp [trace, AddMonoidAlgebra.coeff_single]

private def basis (i : I) : AddMonoidAlgebra R I := AddMonoidAlgebra.single i 1

private theorem basis_zero : basis (R := R) (0 : I) = 1 := rfl

private theorem basis_mul (i j : I) : basis (R := R) i * basis j = basis (i + j) := by
  simp [basis]

private def shift (i : I) (a : AddMonoidAlgebra R I) : AddMonoidAlgebra R I := basis i * a

private theorem shift_zero (a : AddMonoidAlgebra R I) : shift 0 a = a := by
  simp [shift, basis_zero]

private theorem shift_zero_right (i : I) : shift i (0 : AddMonoidAlgebra R I) = 0 := by
  simp [shift]

private theorem shift_add (i : I) (a b : AddMonoidAlgebra R I) :
    shift i (a + b) = shift i a + shift i b := mul_add ..

private theorem shift_neg (i : I) (a : AddMonoidAlgebra R I) : shift i (-a) = -shift i a :=
  mul_neg ..

private theorem shift_comp (i j : I) (a : AddMonoidAlgebra R I) :
    shift i (shift j a) = shift (i + j) a := by
  rw [shift, shift, ← mul_assoc, basis_mul]
  rfl

private theorem shift_mul_shift (i j : I) (a b : AddMonoidAlgebra R I) :
    shift i a * shift j b = shift (i + j) (a * b) := by
  change (basis i * a) * (basis j * b) = basis (i + j) * (a * b)
  rw [← basis_mul]
  ac_rfl

private theorem shift_mul_right (i : I) (a b : AddMonoidAlgebra R I) :
    shift i (a * b) = a * shift i b := by
  simp only [shift]
  ac_rfl

-- The two lamp coordinates shift in opposite directions, preserving their product.
@[ext]
private structure ShiftGroup (f : I → R) where
  a : AddMonoidAlgebra R I
  b : AddMonoidAlgebra R I
  c : R
  t : I

variable {f : I → R}

private def shiftGroupMul (x y : ShiftGroup f) : ShiftGroup f :=
  ⟨x.a + shift x.t y.a, x.b + shift (-x.t) y.b,
    x.c + y.c + trace f (x.a * shift (-x.t) y.b), x.t + y.t⟩

private def shiftGroupInv (x : ShiftGroup f) : ShiftGroup f :=
  ⟨-shift (-x.t) x.a, -shift x.t x.b, -x.c + trace f (x.a * x.b), -x.t⟩

private instance shiftGroupGroup : Group (ShiftGroup f) where
  mul := shiftGroupMul
  one := ⟨0, 0, 0, 0⟩
  inv := shiftGroupInv
  mul_assoc x y z := by
    change shiftGroupMul (shiftGroupMul x y) z = shiftGroupMul x (shiftGroupMul y z)
    have h₁ : -x.t + -y.t = -(x.t + y.t) := by abel
    have h₂ : x.t + -(x.t + y.t) = -y.t := by abel
    apply ShiftGroup.ext
    · simp only [shiftGroupMul, shift_add, shift_comp, add_assoc]
    · simp only [shiftGroupMul, shift_add, shift_comp, h₁, add_assoc]
    · simp only [shiftGroupMul, add_mul, shift_add, shift_comp, mul_add, h₁, shift_mul_shift,
        h₂, shift_mul_right, map_add]
      abel
    · exact add_assoc _ _ _
  one_mul x := by
    change shiftGroupMul ⟨0, 0, 0, 0⟩ x = x
    apply ShiftGroup.ext <;> simp [shiftGroupMul, shift_zero]
  mul_one x := by
    change shiftGroupMul x ⟨0, 0, 0, 0⟩ = x
    apply ShiftGroup.ext <;> simp [shiftGroupMul, shift_zero_right]
  inv_mul_cancel x := by
    change shiftGroupMul (shiftGroupInv x) x = ⟨0, 0, 0, 0⟩
    apply ShiftGroup.ext <;>
      simp [shiftGroupMul, shiftGroupInv, shift_mul_shift, shift_zero, add_assoc]

private theorem mul_apply (x y : ShiftGroup f) : x * y = shiftGroupMul x y := rfl

private theorem inv_apply (x : ShiftGroup f) : x⁻¹ = shiftGroupInv x := rfl

private theorem one_apply : (1 : ShiftGroup f) = ⟨0, 0, 0, 0⟩ := rfl

private def mapLamp (ρ : R →+* S) (σ : I →+ J) :
    AddMonoidAlgebra R I →+* AddMonoidAlgebra S J :=
  (AddMonoidAlgebra.mapDomainRingHom S σ).comp (AddMonoidAlgebra.mapRingHom I ρ)

private theorem mapLamp_single (ρ : R →+* S) (σ : I →+ J) (i : I) (r : R) :
    mapLamp ρ σ (AddMonoidAlgebra.single i r) = AddMonoidAlgebra.single (σ i) (ρ r) := by
  simp [mapLamp]

private theorem mapLamp_shift (ρ : R →+* S) (σ : I →+ J) (i : I)
    (a : AddMonoidAlgebra R I) :
    mapLamp ρ σ (shift i a) = shift (σ i) (mapLamp ρ σ a) := by
  simp [shift, basis, mapLamp_single]

private theorem map_trace (ρ : R →+* S) (σ : I →+ J) {g : J → S}
    (hf : ∀ i, ρ (f i) = g (σ i)) (a : AddMonoidAlgebra R I) :
    ρ (trace f a) = trace g (mapLamp ρ σ a) := by
  obtain ⟨a, rfl⟩ := AddMonoidAlgebra.coeffEquiv.symm.surjective a
  induction a using Finsupp.induction_linear with
  | zero => simp [AddMonoidAlgebra.coeffEquiv]
  | add a b ha hb =>
    change ρ (trace f (AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b)) =
      trace g (mapLamp ρ σ (AddMonoidAlgebra.ofCoeff a + AddMonoidAlgebra.ofCoeff b))
    change ρ (trace f (AddMonoidAlgebra.ofCoeff a)) =
      trace g (mapLamp ρ σ (AddMonoidAlgebra.ofCoeff a)) at ha
    change ρ (trace f (AddMonoidAlgebra.ofCoeff b)) =
      trace g (mapLamp ρ σ (AddMonoidAlgebra.ofCoeff b)) at hb
    simp only [map_add, ha, hb]
  | single i r =>
    change ρ (trace f (AddMonoidAlgebra.single i r)) =
      trace g (mapLamp ρ σ (AddMonoidAlgebra.single i r))
    simp [mapLamp_single, trace_single, hf]

private def mapGroup (ρ : R →+* S) (σ : I →+ J) {g : J → S}
    (hf : ∀ i, ρ (f i) = g (σ i)) : ShiftGroup f →* ShiftGroup g where
  toFun x := ⟨mapLamp ρ σ x.a, mapLamp ρ σ x.b, ρ x.c, σ x.t⟩
  map_one' := by apply ShiftGroup.ext <;> simp [one_apply]
  map_mul' x y := by
    simp only [mul_apply, shiftGroupMul, map_add, map_neg, map_trace ρ σ hf, map_mul,
      mapLamp_shift]

end ShiftGroup


open Multiplicative (ofAdd)

private abbrev Lamps := AddMonoidAlgebra ℤ ℤ

private abbrev Counterexample := ShiftGroup pairingValues

private def firstLamp : Multiplicative Lamps →* Counterexample where
  toFun a := ⟨a.toAdd, 0, 0, 0⟩
  map_one' := rfl
  map_mul' a b := by
    apply ShiftGroup.ext <;> simp [mul_apply, shiftGroupMul, shift_zero]

private def secondLamp : Multiplicative Lamps →* Counterexample where
  toFun b := ⟨0, b.toAdd, 0, 0⟩
  map_one' := rfl
  map_mul' a b := by
    apply ShiftGroup.ext <;> simp [mul_apply, shiftGroupMul, shift_zero]

private def central : Multiplicative ℤ →* Counterexample where
  toFun c := ⟨0, 0, c.toAdd, 0⟩
  map_one' := rfl
  map_mul' x y := by
    apply ShiftGroup.ext <;> simp [mul_apply, shiftGroupMul, shift_zero]

private def time : Multiplicative ℤ →* Counterexample where
  toFun t := ⟨0, 0, 0, t.toAdd⟩
  map_one' := rfl
  map_mul' x y := by
    apply ShiftGroup.ext <;> simp [mul_apply, shiftGroupMul, shift_zero_right]

private theorem timeFirst (i : ℤ) (a : Lamps) :
    time (ofAdd i) * firstLamp (ofAdd a) * time (ofAdd (-i)) =
      firstLamp (ofAdd (shift i a)) := by
  apply ShiftGroup.ext <;>
    simp [mul_apply, shiftGroupMul, shift_zero_right, time, firstLamp]

private theorem timeSecond (i : ℤ) (b : Lamps) :
    time (ofAdd i) * secondLamp (ofAdd b) * time (ofAdd (-i)) =
      secondLamp (ofAdd (shift (-i) b)) := by
  apply ShiftGroup.ext <;>
    simp [mul_apply, shiftGroupMul, shift_zero_right, time, secondLamp]

private theorem shift_basis (i j : ℤ) : shift i (basis (R := ℤ) j) = basis (i + j) :=
  basis_mul i j

private theorem zpow_integer (φ : Multiplicative ℤ →* Counterexample) (i : ℤ) :
    φ (ofAdd i) = φ (ofAdd 1) ^ i := by
  rw [← map_zpow, ← ofAdd_zsmul, zsmul_eq_mul, mul_one]
  rfl

private theorem lamps_mem {K : Subgroup Counterexample} (L : Multiplicative Lamps →* Counterexample)
    (h : ∀ i : ℤ, L (ofAdd (basis i)) ∈ K) (a : Lamps) : L (ofAdd a) ∈ K := by
  induction a using AddMonoidAlgebra.induction_on with
  | of i => exact h i
  | add a b ha hb => simpa only [ofAdd_add, map_mul] using K.mul_mem ha hb
  | smul r a ha =>
    simpa only [ofAdd_zsmul, map_zpow] using K.zpow_mem ha r

private theorem counterexample_fg : Group.FG Counterexample := by
  let generators : Set Counterexample :=
    {firstLamp (ofAdd (basis 0)), secondLamp (ofAdd (basis 0)), central (ofAdd 1), time (ofAdd 1)}
  let K := Subgroup.closure generators
  refine Group.fg_iff.mpr ⟨generators, ?_, by simp [generators]⟩
  have hfirst : firstLamp (ofAdd (basis 0)) ∈ K := Subgroup.subset_closure (by simp [generators])
  have hsecond : secondLamp (ofAdd (basis 0)) ∈ K := Subgroup.subset_closure (by simp [generators])
  have hcentral : central (ofAdd 1) ∈ K := Subgroup.subset_closure (by simp [generators])
  have htime : time (ofAdd 1) ∈ K := Subgroup.subset_closure (by simp [generators])
  have ht (i : ℤ) : time (ofAdd i) ∈ K := zpow_integer time i ▸ K.zpow_mem htime i
  have hc (i : ℤ) : central (ofAdd i) ∈ K := zpow_integer central i ▸ K.zpow_mem hcentral i
  have ha := lamps_mem (K := K) firstLamp fun i ↦ by
    simpa only [timeFirst, shift_basis, add_zero] using
      K.mul_mem (K.mul_mem (ht i) hfirst) (ht (-i))
  have hb := lamps_mem (K := K) secondLamp fun i ↦ by
    have h := K.mul_mem (K.mul_mem (ht (-i)) hsecond) (ht (-(-i)))
    rwa [timeSecond, neg_neg, shift_basis, add_zero] at h
  apply top_unique
  intro x _
  have hx : firstLamp (ofAdd x.a) * secondLamp (ofAdd x.b) *
      central (ofAdd (x.c - trace pairingValues (x.a * x.b))) * time (ofAdd x.t) = x := by
    apply ShiftGroup.ext <;>
      simp [mul_apply, shiftGroupMul, shift_zero, firstLamp, secondLamp, central, time]
  exact hx ▸ K.mul_mem (K.mul_mem (K.mul_mem (ha x.a) (hb x.b)) (hc _)) (ht _)

-- Reduce both the group ring coefficients and the shift indices modulo the same integer.
private def modGroup (m : ℕ) (hm : 0 < m) :
    Counterexample →* ShiftGroup (fun x : ZMod m ↦ (pairingValues (ZMod.cast x) : ZMod m)) :=
  mapGroup (Int.castRingHom _) (Int.castAddHom _) fun i ↦
    pairingValues_cast_eq hm (ZMod.intCast_zmod_cast (i : ZMod m)).symm

private def coordinates {R I : Type*} [CommRing R] [AddCommGroup I] (f : I → R) :
    ShiftGroup f ≃ (AddMonoidAlgebra R I × AddMonoidAlgebra R I × R × I) where
  toFun x := ⟨x.a, x.b, x.c, x.t⟩
  invFun x := ⟨x.1, x.2.1, x.2.2.1, x.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

private theorem card_modGroup (p k : ℕ) [NeZero (p ^ k)] (f : ZMod (p ^ k) → ZMod (p ^ k)) :
    Nat.card (ShiftGroup f) = p ^ (k * p ^ k + k * p ^ k + k + k) := by
  have hc : Nat.card (AddMonoidAlgebra (ZMod (p ^ k)) (ZMod (p ^ k))) = p ^ (k * p ^ k) := by
    rw [Nat.card_congr (AddMonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite),
      Nat.card_fun, Nat.card_zmod, ← pow_mul]
  rw [Nat.card_congr (coordinates f)]
  simp only [Nat.card_prod, hc, Nat.card_zmod, pow_add, mul_assoc]

private theorem cast_ne_zero_of_lt {a : ℤ} {m : ℕ} (ha : a ≠ 0) (h : a.natAbs < m) :
    (a : ZMod m) ≠ 0 := by
  rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd, Int.natCast_dvd]
  exact fun hd ↦ (not_le_of_gt h) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha) hd)

private theorem lamp_separated {p : ℕ} (hp : 1 < p) {a : Lamps} (ha : a ≠ 0) :
    ∃ k : ℕ, mapLamp (Int.castRingHom (ZMod (p ^ k))) (Int.castAddHom (ZMod (p ^ k))) a ≠ 0 := by
  classical
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr
    (show a.coeff ≠ 0 from fun h ↦ ha (AddMonoidAlgebra.coeffEquiv.injective h))
  let B := ∑ j ∈ a.coeff.support, j.natAbs
  have hB {j : ℤ} (hj : j ∈ a.coeff.support) : j.natAbs ≤ B :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hj
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (max (2 * B) (a.coeff i).natAbs) hp
  let m := p ^ k
  let ρ := Int.castRingHom (ZMod m)
  let σ := Int.castAddHom (ZMod m)
  let a' := AddMonoidAlgebra.mapRingHom ℤ ρ a
  have h_inj : Set.InjOn σ (a.coeff.support : Set ℤ) := by
    intro j hj l hl hjl
    change (j : ZMod m) = (l : ZMod m) at hjl
    by_contra hn
    have hlt : (j - l).natAbs < m := by
      have hb := (max_lt_iff.mp hk).1
      have hj' := hB hj
      have hl' := hB hl
      omega
    exact cast_ne_zero_of_lt (sub_ne_zero.mpr hn) hlt (by simp [hjl])
  have hs : (a'.coeff.support : Set ℤ) ⊆ a.coeff.support := by
    intro j hj
    simp only [Finset.mem_coe, Finsupp.mem_support_iff, a', AddMonoidAlgebra.coeff_mapRingHom]
      at hj ⊢
    exact fun hz ↦ hj (by simp [hz])
  have hcoeff : (mapLamp ρ σ a).coeff (σ i) = ρ (a.coeff i) :=
    (Finsupp.mapDomain_apply' (a.coeff.support : Set ℤ) a'.coeff hs h_inj hi).trans
      (AddMonoidAlgebra.coeff_mapRingHom ρ a i)
  refine ⟨k, fun h ↦ ?_⟩
  have hz : (a.coeff i : ZMod m) ≠ 0 :=
    cast_ne_zero_of_lt (Finsupp.mem_support_iff.mp hi) (max_lt_iff.mp hk).2
  change mapLamp ρ σ a = 0 at h
  rw [h, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hcoeff
  exact hz hcoeff.symm

private theorem modGroup_separates {p : ℕ} (hp : p.Prime) {x : Counterexample} (hx : x ≠ 1) :
    ∃ (k : ℕ) (hm : 0 < p ^ k), modGroup (p ^ k) hm x ≠ 1 := by
  have hm (k : ℕ) : 0 < p ^ k := pow_pos hp.pos _
  by_contra! h
  apply hx
  apply ShiftGroup.ext
  · change x.a = 0
    by_contra ha
    obtain ⟨k, hk⟩ := lamp_separated hp.one_lt ha
    exact hk (congrArg ShiftGroup.a (h k (hm k)))
  · change x.b = 0
    by_contra hb
    obtain ⟨k, hk⟩ := lamp_separated hp.one_lt hb
    exact hk (congrArg ShiftGroup.b (h k (hm k)))
  · change x.c = 0
    by_contra hc
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x.c.natAbs hp.one_lt
    exact cast_ne_zero_of_lt hc hk (congrArg ShiftGroup.c (h k (hm k)))
  · change x.t = 0
    by_contra ht
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt x.t.natAbs hp.one_lt
    exact cast_ne_zero_of_lt ht hk (congrArg ShiftGroup.t (h k (hm k)))

private theorem residually_p (p : ℕ) (hp : p.Prime) (x : Counterexample) (hx : x ≠ 1) :
    ∃ (N : Subgroup Counterexample) (_ : N.Normal), x ∉ N ∧
      Finite (Counterexample ⧸ N) ∧ IsPGroup p (Counterexample ⧸ N) := by
  obtain ⟨k, hm, hk⟩ := modGroup_separates hp hx
  let : NeZero (p ^ k) := ⟨hm.ne'⟩
  let φ := modGroup (p ^ k) hm
  have : Finite (AddMonoidAlgebra (ZMod (p ^ k)) (ZMod (p ^ k))) :=
    Finite.of_equiv _ (AddMonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite).symm
  have : Finite (ShiftGroup (fun x : ZMod (p ^ k) ↦
      (pairingValues (ZMod.cast x) : ZMod (p ^ k)))) :=
    Finite.of_equiv _ (coordinates _).symm
  let e := QuotientGroup.quotientKerEquivRange φ
  refine ⟨φ.ker, inferInstance, hk, Finite.of_injective e e.injective, ?_⟩
  exact ((IsPGroup.of_card (card_modGroup p k _)).to_subgroup φ.range).of_equiv e.symm

-- A commutator with the shift takes a first-coordinate element to its forward difference.
private def deltaLamp (a : Lamps) : Lamps := shift 1 a - a

private theorem commutator_time_first (a : Lamps) :
    ⁅time (ofAdd 1), firstLamp (ofAdd a)⁆ = firstLamp (ofAdd (deltaLamp a)) := by
  rw [commutatorElement_def, ← time.map_inv, ← firstLamp.map_inv]
  change time (ofAdd 1) * firstLamp (ofAdd a) * time (ofAdd (-1)) *
    firstLamp (ofAdd (-a)) = _
  rw [timeFirst, ← map_mul, ← ofAdd_add, ← sub_eq_add_neg]
  rfl

private theorem commutator_first_second (a b : Lamps) :
    ⁅firstLamp (ofAdd a), secondLamp (ofAdd b)⁆ =
      central (ofAdd (trace pairingValues (a * b))) := by
  rw [commutatorElement_def, ← firstLamp.map_inv, ← secondLamp.map_inv]
  change firstLamp (ofAdd a) * secondLamp (ofAdd b) * firstLamp (ofAdd (-a)) *
    secondLamp (ofAdd (-b)) = _
  apply ShiftGroup.ext <;>
    simp [mul_apply, shiftGroupMul, firstLamp, secondLamp, central, shift_zero]

private theorem trace_iter_delta (n : ℕ) (a : Lamps) (i : ℤ) :
    trace pairingValues (shift i (deltaLamp^[n] a)) =
      (fwdDiff (1 : ℤ))^[n] (fun j ↦ trace pairingValues (shift j a)) i := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have h (b : Lamps) : shift i (deltaLamp b) = shift (i + 1) b - shift i b := by
      change shift i (shift 1 b - b) = _
      rw [sub_eq_add_neg, shift_add, shift_comp, shift_neg, ← sub_eq_add_neg]
    rw [h, map_sub, ih, ih, fwdDiff]

private theorem trace_iter_basis (n : ℕ) :
    trace pairingValues (deltaLamp^[2 * n] (basis (-(n : ℤ)))) =
      (n.factorial : ℤ) * ((2 * n).factorial : ℤ) := by
  have h : (fun j : ℤ ↦ trace pairingValues (shift j (basis (-(n : ℤ))))) =
      fun j ↦ pairingValues (j + -(n : ℤ)) := by
    funext j
    rw [shift_basis]
    simp [basis, trace_single]
  simpa only [shift_zero, h, fwdDiff_iter_comp_add, zero_add, pairingValues_diff] using
    trace_iter_delta (2 * n) (basis (-(n : ℤ))) 0

private theorem iter_delta_mem {G : Type*} [Group G] (φ : Counterexample →* G)
    (a : Lamps) (n : ℕ) :
    φ (firstLamp (ofAdd (deltaLamp^[n] a))) ∈ (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ← commutator_time_first, map_commutatorElement,
      Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) ih

private theorem central_mem_lowerCentralSeries {G : Type*} [Group G] (φ : Counterexample →* G)
    (n : ℕ) :
    φ (central (ofAdd ((n.factorial : ℤ) * ((2 * n).factorial : ℤ)))) ∈
      (⊤ : Subgroup G).lowerCentralSeries (2 * n + 1) := by
  rw [← trace_iter_basis n]
  have h := Subgroup.commutator_mem_commutator
    (iter_delta_mem φ (basis (-(n : ℤ))) (2 * n))
    (Subgroup.mem_top (φ (secondLamp (ofAdd (basis 0)))))
  rwa [← Subgroup.lowerCentralSeries_succ, ← map_commutatorElement,
    commutator_first_second, basis_zero, mul_one] at h

private theorem central_not_separated (N : Subgroup Counterexample) [N.Normal]
    (hN : Group.IsNilpotent (Counterexample ⧸ N))
    (ht : ∀ y : Counterexample ⧸ N, y ≠ 1 → ¬ IsOfFinOrder y) :
    central (ofAdd 1) ∈ N := by
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp hN
  let φ := QuotientGroup.mk' N
  have hz := central_mem_lowerCentralSeries φ n
  have hbot : (⊤ : Subgroup (Counterexample ⧸ N)).lowerCentralSeries (2 * n + 1) = ⊥ :=
    le_bot_iff.mp (hn ▸ Subgroup.lowerCentralSeries_antitone ⊤ (show n ≤ 2 * n + 1 by omega))
  rw [hbot, Subgroup.mem_bot, zpow_integer, map_zpow] at hz
  have hfin : IsOfFinOrder (φ (central (ofAdd 1))) :=
    isOfFinOrder_iff_zpow_eq_one.mpr ⟨_, by exact_mod_cast
      (Nat.mul_ne_zero (Nat.factorial_ne_zero n) (Nat.factorial_ne_zero (2 * n))), hz⟩
  exact (QuotientGroup.eq_one_iff _).1 (by by_contra h; exact ht _ h hfin)

/--
**Residual $p$-finiteness for all $p$ does not imply residual torsion-free nilpotence.** It is not
the case that every finitely generated group that is residually a finite $p$-group for every prime
$p$ is residually torsion-free nilpotent. Here a group $G$ is residually a finite $p$-group when
every element $g \ne 1$ lies outside some normal subgroup $N$ such that $G/N$ is a finite
$p$-group, and residually torsion-free nilpotent when every element $g \ne 1$ lies outside some
normal subgroup $N$ such that $G/N$ is nilpotent and has no nontrivial elements of finite order.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems,
Problem 14.52 (Yu. V. Kuz'min); resolution: B. Hartley, in: Symposia Mathematica XVII (Convegno sui
Gruppi Infiniti, INDAM, Roma, 1973), Academic Press, London, 1976, 225-234, Kourovka Archive,
Problem 14.52 (answer: Not always).
-/
theorem residuallyFinitePImpliesResiduallyTorsionFreeNilpotent_refuted :
    ¬ residuallyFinitePImpliesResiduallyTorsionFreeNilpotent := by
  intro h
  have hz : central (ofAdd 1) ≠ 1 := by
    intro he
    have hc : (1 : ℤ) = 0 := congrArg ShiftGroup.c he
    exact one_ne_zero hc
  obtain ⟨N, hNormal, hNotMem, hNilpotent, hTorsionFree⟩ :=
    h Counterexample counterexample_fg residually_p (central (ofAdd 1)) hz
  exact hNotMem (central_not_separated N hNilpotent hTorsionFree)

end

end MathlibExt.GroupTheory.ResiduallyFinitePGroupTorsionFreeNilpotentKourovka14Problem52Wanted
