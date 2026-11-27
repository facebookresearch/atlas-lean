/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.Tactic

/-!
# Engel lengths of products admit no polynomial bound (Kourovka 11.88)

Kourovka Notebook, Archive of Solved Problems, Problem 11.88 (V. A. Roman'kov): the length `l(g)` of
an Engel element `g` is the least `l` with `[h, g; l] = 1` for all `h`. Is there a polynomial
`φ(x, y)` with `l(uv) ≤ φ(l(u), l(v))`?

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.88 (V. A.
Roman'kov). UnsolvedMath record UM-00700780 (`KOU-11.88`), dataset ulamai/UnsolvedMath v1.8.0.

Engel elements are bounded ones, as in the source and in Dolbak's Definition 1: `[h, g; l] = 1` for
all `h` and some `l ≥ 1`, with `[h, g; 1] = [h, g] = h⁻¹ g⁻¹ h g` and
`[h, g; i + 1] = [[h, g; i], g]`. The polynomial is chosen for each group, as in A. Abdollahi's
survey (Engel elements in groups, arXiv:1002.0309, before Problem 3.27): Roman'kov "asked whether
for any group G there exists a linear (polynomial) function φ(x, y)" with `l(uv) ≤ φ(l(u), l(v))`
for Engel elements `u`, `v` of `G`. The bound is required when `uv` is also Engel, since `l(uv)` is
defined only then; whether products of Engel elements are Engel is left open, as the source notes. A
polynomial serving all groups would serve each group, so the refutation also refutes that reading.
Natural coefficients lose nothing, since on `ℕ²` every real polynomial is bounded by one with
natural coefficients.

The main result is `engelLengthPolynomialBound_refuted`, proved here with a direct construction:
for each `n`, the wreath product of the functions `ZMod (2 ^ n) → ZMod 2` with the dihedral group
of order `2 ^ (n + 1)` contains the reflection `u` and the reflection `v` whose product is the
translation by `1`; the reflections have Engel length at most `n + 2`, while the product has Engel
length at least `2 ^ n`, which exceeds every polynomial in the lengths of the factors.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted

/-- **Commutator for Engel lengths.** For elements $x$ and $y$ of a group, the commutator is
$[x, y] = x^{-1} y^{-1} x y$ (the convention of the Kourovka Notebook). -/
def kcomm {G : Type*} [Group G] (x y : G) : G := x⁻¹ * y⁻¹ * x * y

/-- **Iterated commutators for Engel lengths.** For elements $h$ and $g$ of a group and a natural
number $l$, the iterated commutator $[h, g; l]$ is defined by $[h, g; 0] = h$ and
$[h, g; l + 1] = [[h, g; l], g]$, where $[x, y] = x^{-1} y^{-1} x y$; in particular
$[h, g; 1] = [h, g]$. -/
def engelComm {G : Type*} [Group G] (h g : G) : ℕ → G
  | 0 => h
  | l + 1 => kcomm (engelComm h g l) g

/-- **Bounded Engel element.** An element $g$ of a group $G$ is an Engel element if there is an
$l \ge 1$ such that $[h, g; l] = 1$ for every $h \in G$, where $[h, g; 0] = h$,
$[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$. -/
def IsEngel {G : Type*} [Group G] (g : G) : Prop :=
  ∃ l : ℕ, 1 ≤ l ∧ ∀ h : G, engelComm h g l = 1

/-- **Engel length.** For an element $g$ of a group $G$, the Engel length $l(g)$ is the least
$k \ge 1$ such that $[h, g; k] = 1$ for every $h \in G$, where $[h, g; 0] = h$,
$[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$. If no such $k$ exists, that
is, if $g$ is not an Engel element, then $l(g) = 0$. -/
noncomputable def engelLength {G : Type*} [Group G] (g : G) : ℕ :=
  sInf {l | 1 ≤ l ∧ ∀ h : G, engelComm h g l = 1}

/-- **Roman'kov's problem on Engel lengths of products (Kourovka 11.88).** The statement that every
group $G$ has a polynomial $\varphi(x, y)$ in two variables with natural-number coefficients such
that $l(uv) \le \varphi(l(u), l(v))$ for all $u, v \in G$ for which $u$, $v$ and $uv$ are Engel
elements. Here $g \in G$ is an Engel element if there is a $k \ge 1$ with $[h, g; k] = 1$ for all
$h \in G$, and its Engel length $l(g)$ is the least such $k$, where $[h, g; 0] = h$,
$[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$.

Natural coefficients lose nothing: on $\mathbb{N}^2$ every real polynomial is bounded by one with
natural coefficients. -/
def engelLengthPolynomialBound : Prop :=
  ∀ (G : Type) [Group G], ∃ φ : MvPolynomial (Fin 2) ℕ, ∀ u v : G, IsEngel u → IsEngel v →
    IsEngel (u * v) → engelLength (u * v) ≤ MvPolynomial.eval ![engelLength u, engelLength v] φ

/-! ### The dihedral wreath construction -/

variable {n : ℕ}

/-- The action of the dihedral group on `ZMod (2 ^ n)` by affine maps: rotations translate and
reflections negate. -/
private def dihedralAct (n : ℕ) : DihedralGroup (2 ^ n) → ZMod (2 ^ n) → ZMod (2 ^ n)
  | .r i, x => x + i
  | .sr i, x => -x - i

private theorem dihedralAct_mul (n : ℕ) (a b : DihedralGroup (2 ^ n)) (x : ZMod (2 ^ n)) :
    dihedralAct n (a * b) x = dihedralAct n a (dihedralAct n b x) := by
  obtain (i | i) := a <;> obtain (j | j) := b <;> simp [dihedralAct] <;> ring

private theorem dihedralAct_one (n : ℕ) (x : ZMod (2 ^ n)) :
    dihedralAct n 1 x = x := by
  simp only [← DihedralGroup.r_zero, dihedralAct, add_zero]

/-- The action of the dihedral group on functions `ZMod (2 ^ n) → ZMod 2` by precomposition
with the inverse affine map. -/
private def wreathSmul (n : ℕ) (g : DihedralGroup (2 ^ n)) (a : ZMod (2 ^ n) → ZMod 2) :
    ZMod (2 ^ n) → ZMod 2 :=
  fun x => a (dihedralAct n g⁻¹ x)

private theorem wreathSmul_add (n : ℕ) (g : DihedralGroup (2 ^ n))
    (a b : ZMod (2 ^ n) → ZMod 2) :
    wreathSmul n g (a + b) = wreathSmul n g a + wreathSmul n g b := by
  funext x
  simp [wreathSmul, Pi.add_apply]

private theorem wreathSmul_sub (n : ℕ) (g : DihedralGroup (2 ^ n))
    (a b : ZMod (2 ^ n) → ZMod 2) :
    wreathSmul n g (a - b) = wreathSmul n g a - wreathSmul n g b := by
  funext x
  simp [wreathSmul, Pi.sub_apply]

private theorem wreathSmul_zero (n : ℕ) (g : DihedralGroup (2 ^ n)) :
    wreathSmul n g 0 = 0 := by
  funext x
  simp [wreathSmul]

private theorem wreathSmul_smul (n : ℕ) (g h : DihedralGroup (2 ^ n))
    (a : ZMod (2 ^ n) → ZMod 2) :
    wreathSmul n g (wreathSmul n h a) = wreathSmul n (g * h) a := by
  funext x
  simp [wreathSmul, mul_inv_rev, dihedralAct_mul]

private theorem wreathSmul_one (n : ℕ) (a : ZMod (2 ^ n) → ZMod 2) :
    wreathSmul n 1 a = a := by
  funext x
  simp [wreathSmul, dihedralAct_one]

/-- An element of the wreath product: a function `ZMod (2 ^ n) → ZMod 2` together with a
dihedral element acting on it. -/
@[ext]
private structure Wreath (n : ℕ) where
  toFun : ZMod (2 ^ n) → ZMod 2
  toDihedral : DihedralGroup (2 ^ n)

private def wreathMul (x y : Wreath n) : Wreath n :=
  ⟨x.toFun + wreathSmul n x.toDihedral y.toFun, x.toDihedral * y.toDihedral⟩

private def wreathOne : Wreath n :=
  ⟨0, 1⟩

private def wreathInv (x : Wreath n) : Wreath n :=
  ⟨-(wreathSmul n x.toDihedral⁻¹ x.toFun), x.toDihedral⁻¹⟩

private instance : Mul (Wreath n) :=
  ⟨wreathMul⟩

private instance : One (Wreath n) :=
  ⟨wreathOne⟩

private instance : Inv (Wreath n) :=
  ⟨wreathInv⟩

private theorem wreath_mul_toFun (x y : Wreath n) :
    (x * y).toFun = x.toFun + wreathSmul n x.toDihedral y.toFun :=
  rfl

private theorem wreath_mul_toDihedral (x y : Wreath n) :
    (x * y).toDihedral = x.toDihedral * y.toDihedral :=
  rfl

private theorem wreath_inv_toFun (x : Wreath n) :
    x⁻¹.toFun = -(wreathSmul n x.toDihedral⁻¹ x.toFun) :=
  rfl

private theorem wreath_inv_toDihedral (x : Wreath n) :
    x⁻¹.toDihedral = x.toDihedral⁻¹ :=
  rfl

private theorem wreath_one_toFun : (1 : Wreath n).toFun = 0 :=
  rfl

private theorem wreath_one_toDihedral : (1 : Wreath n).toDihedral = 1 :=
  rfl

private instance : Group (Wreath n) where
  mul_assoc x y z := by
    apply Wreath.ext
    · simp only [wreath_mul_toFun, wreath_mul_toDihedral, wreathSmul_add, wreathSmul_smul,
        add_assoc]
    · simp only [wreath_mul_toDihedral, mul_assoc]
  one_mul x := by
    apply Wreath.ext
    · simp only [wreath_mul_toFun, wreath_one_toFun, wreath_one_toDihedral,
        wreathSmul_one, zero_add]
    · simp only [wreath_mul_toDihedral, wreath_one_toDihedral, one_mul]
  mul_one x := by
    apply Wreath.ext
    · simp only [wreath_mul_toFun, wreath_one_toFun, wreathSmul_zero, add_zero]
    · simp only [wreath_mul_toDihedral, wreath_one_toDihedral, mul_one]
  inv_mul_cancel x := by
    apply Wreath.ext
    · simp only [wreath_mul_toFun, wreath_inv_toFun, wreath_inv_toDihedral,
        wreath_one_toFun, neg_add_cancel]
    · simp only [wreath_mul_toDihedral, wreath_inv_toDihedral, wreath_one_toDihedral,
        inv_mul_cancel]

/-! ### Iterated commutators in the wreath product -/

private theorem engelComm_succ {G : Type*} [Group G] (h g : G) (k : ℕ) :
    engelComm h g (k + 1) = kcomm (engelComm h g k) g :=
  rfl

private theorem engelComm_add {G : Type*} [Group G] (h g : G) (k j : ℕ) :
    engelComm h g (k + j) = engelComm (engelComm h g k) g j := by
  induction j with
  | zero => simp [engelComm]
  | succ j ih => exact congrArg (fun z => kcomm z g) ih

private theorem kcomm_one {G : Type*} [Group G] (x : G) : kcomm x 1 = 1 := by
  simp [kcomm]

private theorem engelComm_one_succ {G : Type*} [Group G] (h : G) (k : ℕ) :
    engelComm h 1 (k + 1) = 1 := by
  simp [engelComm, kcomm_one]

private theorem engelComm_pi_apply {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]
    (h g : ∀ i, G i) (k : ℕ) (i : ι) :
    engelComm h g k i = engelComm (h i) (g i) k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [engelComm, kcomm, Pi.mul_apply, Pi.inv_apply, ih]

private theorem wreath_kcomm_toDihedral (x y : Wreath n) :
    (kcomm x y).toDihedral = kcomm x.toDihedral y.toDihedral := by
  simp only [kcomm, wreath_mul_toDihedral, wreath_inv_toDihedral]

private theorem engelComm_toDihedral (x y : Wreath n) (k : ℕ) :
    (engelComm x y k).toDihedral = engelComm x.toDihedral y.toDihedral k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [engelComm, wreath_kcomm_toDihedral, ih]

/-- The difference operator of a dihedral element on the function part: `h • a - a`. -/
private def diffOp (n : ℕ) (h : DihedralGroup (2 ^ n)) (a : ZMod (2 ^ n) → ZMod 2) :
    ZMod (2 ^ n) → ZMod 2 :=
  wreathSmul n h⁻¹ a - a

private theorem kcomm_wreath_eq_diffOp {a : ZMod (2 ^ n) → ZMod 2}
    {h : DihedralGroup (2 ^ n)} :
    kcomm (⟨a, 1⟩ : Wreath n) (⟨0, h⟩ : Wreath n) = ⟨diffOp n h a, 1⟩ := by
  apply Wreath.ext
  · simp only [kcomm, wreath_mul_toFun, wreath_inv_toFun, wreath_inv_toDihedral,
      wreath_mul_toDihedral, wreathSmul_one, wreathSmul_zero, add_zero, one_mul, mul_one,
      inv_one, diffOp]
    abel
  · simp only [kcomm, wreath_mul_toDihedral, wreath_inv_toDihedral, inv_one, one_mul,
      mul_one, inv_mul_cancel]

private theorem engelComm_wreath_eq_diffOp_iterate (a : ZMod (2 ^ n) → ZMod 2)
    (h : DihedralGroup (2 ^ n)) (k : ℕ) :
    engelComm (⟨a, 1⟩ : Wreath n) (⟨0, h⟩ : Wreath n) k =
      ⟨(diffOp n h)^[k] a, 1⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [engelComm, ih, kcomm_wreath_eq_diffOp, Function.iterate_succ_apply']

/-! ### Engel lengths in the dihedral group -/

private theorem dihedral_kcomm_sr (t : ZMod (2 ^ n)) (g : DihedralGroup (2 ^ n)) :
    ∃ w : ZMod (2 ^ n), kcomm g (DihedralGroup.sr t) = DihedralGroup.r (2 * w) := by
  obtain (i | i) := g
  · refine ⟨-i, ?_⟩
    unfold kcomm
    rw [DihedralGroup.inv_r, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr,
      DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    congr 1
    ring
  · refine ⟨t - i, ?_⟩
    simp only [kcomm, DihedralGroup.inv_sr, DihedralGroup.sr_mul_sr,
      DihedralGroup.r_mul_sr]
    congr 1
    ring

private theorem dihedral_kcomm_r_sr (t u : ZMod (2 ^ n)) :
    kcomm (DihedralGroup.r u) (DihedralGroup.sr t) = DihedralGroup.r (-2 * u) := by
  unfold kcomm
  rw [DihedralGroup.inv_r, DihedralGroup.inv_sr, DihedralGroup.r_mul_sr,
    DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
  congr 1
  ring

private theorem dihedral_engelComm_sr (t : ZMod (2 ^ n)) (g : DihedralGroup (2 ^ n)) (k : ℕ)
    (hk : 1 ≤ k) :
    ∃ w : ZMod (2 ^ n), engelComm g (DihedralGroup.sr t) k =
      DihedralGroup.r ((2 : ZMod (2 ^ n)) ^ k * w) := by
  induction k with
  | zero => omega
  | succ k ih =>
    cases k with
    | zero =>
      obtain ⟨w, hw⟩ := dihedral_kcomm_sr t g
      refine ⟨w, ?_⟩
      simp [engelComm, hw]
    | succ k =>
      obtain ⟨w, hw⟩ := ih (by omega)
      refine ⟨-w, ?_⟩
      rw [engelComm_succ, hw, dihedral_kcomm_r_sr]
      congr 1
      ring

private theorem dihedral_engelComm_sr_eq_one {t : ZMod (2 ^ n)} {g : DihedralGroup (2 ^ n)}
    {k : ℕ} (hk : n ≤ k) (hk1 : 1 ≤ k) :
    engelComm g (DihedralGroup.sr t) k = 1 := by
  obtain ⟨w, hw⟩ := dihedral_engelComm_sr t g k hk1
  rw [hw]
  have h2n : (2 : ZMod (2 ^ n)) ^ n = 0 := by
    have h : (2 : ZMod (2 ^ n)) ^ n = ((2 ^ n : ℕ) : ZMod (2 ^ n)) := by
      push_cast
      ring
    exact h.trans (ZMod.natCast_self _)
  have h2 : (2 : ZMod (2 ^ n)) ^ k = 0 := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [pow_add, h2n, zero_mul]
  rw [h2, zero_mul, DihedralGroup.r_zero]

private theorem dihedral_engelComm_r_one (g : DihedralGroup (2 ^ n)) :
    engelComm g (DihedralGroup.r 1) 2 = 1 := by
  obtain (i | i) := g <;> simp [engelComm, kcomm]

/-! ### Difference operators on the function part -/

private theorem wreathSmul_sr_apply (t : ZMod (2 ^ n)) (a : ZMod (2 ^ n) → ZMod 2)
    (x : ZMod (2 ^ n)) :
    wreathSmul n (DihedralGroup.sr t) a x = a (-x - t) := by
  simp [wreathSmul, dihedralAct]

private theorem zmod2_sub_sub : ∀ u v w : ZMod 2, (u - v) - (v - w) = u - w := by
  decide

private theorem diffOp_sr_sq (t : ZMod (2 ^ n)) (a : ZMod (2 ^ n) → ZMod 2) :
    diffOp n (DihedralGroup.sr t) (diffOp n (DihedralGroup.sr t) a) = 0 := by
  funext x
  simp only [diffOp, Pi.sub_apply, DihedralGroup.inv_sr, wreathSmul_sr_apply]
  rw [show -(-x - t) - t = x by ring]
  have h2 : ∀ u v : ZMod 2, (u - v) - (v - u) = 0 := by decide
  exact h2 _ _

private theorem wreath_engelComm_sr (hn : 1 ≤ n) (t : ZMod (2 ^ n)) (x : Wreath n) :
    engelComm x ⟨0, DihedralGroup.sr t⟩ (n + 2) = 1 := by
  have hdi : (engelComm x ⟨0, DihedralGroup.sr t⟩ n).toDihedral = 1 := by
    rw [engelComm_toDihedral]
    exact dihedral_engelComm_sr_eq_one le_rfl hn
  have hy : engelComm x ⟨0, DihedralGroup.sr t⟩ n =
      ⟨(engelComm x ⟨0, DihedralGroup.sr t⟩ n).toFun, 1⟩ :=
    Wreath.ext rfl hdi
  rw [engelComm_add, hy, engelComm_wreath_eq_diffOp_iterate]
  have h2 : (diffOp n (DihedralGroup.sr t))^[2]
      (engelComm x ⟨0, DihedralGroup.sr t⟩ n).toFun = 0 := by
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_zero_apply]
    exact diffOp_sr_sq t _
  rw [h2]
  rfl

/-- The shift operator on functions, given by precomposition with translation by `1`. -/
private def shiftOp (n : ℕ) (a : ZMod (2 ^ n) → ZMod 2) : ZMod (2 ^ n) → ZMod 2 :=
  wreathSmul n (DihedralGroup.r (-1)) a

private theorem shiftOp_sub (a b : ZMod (2 ^ n) → ZMod 2) :
    shiftOp n (a - b) = shiftOp n a - shiftOp n b :=
  wreathSmul_sub n _ _ _

private theorem shiftOp_iterate_sub (m : ℕ) (a b : ZMod (2 ^ n) → ZMod 2) :
    (shiftOp n)^[m] (a - b) = (shiftOp n)^[m] a - (shiftOp n)^[m] b := by
  induction m with
  | zero => simp
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ih, shiftOp, wreathSmul_sub]

private theorem shiftOp_iterate (m : ℕ) (a : ZMod (2 ^ n) → ZMod 2) :
    (shiftOp n)^[m] a =
      wreathSmul n ((DihedralGroup.r (-1) : DihedralGroup (2 ^ n)) ^ m) a := by
  induction m with
  | zero => simp [wreathSmul_one]
  | succ m ih =>
    simp only [Function.iterate_succ_apply', ih, shiftOp, wreathSmul_smul, pow_succ']

private theorem dihedral_r_neg_one_pow (m : ℕ) :
    (DihedralGroup.r (-1) : DihedralGroup (2 ^ n)) ^ m =
      DihedralGroup.r (-(m : ZMod (2 ^ n))) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, DihedralGroup.r_mul_r]
    congr 1
    push_cast
    ring

private theorem shiftOp_iterate_pow (a : ZMod (2 ^ n) → ZMod 2) :
    (shiftOp n)^[2 ^ n] a = a := by
  rw [shiftOp_iterate, dihedral_r_neg_one_pow]
  have h0 : (-((2 ^ n : ℕ) : ZMod (2 ^ n))) = 0 := by
    rw [ZMod.natCast_self, neg_zero]
  rw [h0, DihedralGroup.r_zero, wreathSmul_one]

private theorem diffOp_iterate_pow (k : ℕ) :
    ∀ a : ZMod (2 ^ n) → ZMod 2,
      (diffOp n (DihedralGroup.r 1))^[2 ^ k] a = (shiftOp n)^[2 ^ k] a - a := by
  induction k with
  | zero =>
    intro a
    simp only [pow_zero, Function.iterate_one]
    rfl
  | succ k ih =>
    intro a
    have h2k : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by
      rw [pow_succ]
      exact mul_two _
    rw [h2k, Function.iterate_add_apply, ih, ih, shiftOp_iterate_sub,
      Function.iterate_add_apply]
    funext x
    simp only [Pi.sub_apply]
    exact zmod2_sub_sub _ _ _

private theorem diffOp_iterate_pow_eq_zero (a : ZMod (2 ^ n) → ZMod 2) :
    (diffOp n (DihedralGroup.r 1))^[2 ^ n] a = 0 := by
  rw [diffOp_iterate_pow, shiftOp_iterate_pow, sub_self]

private theorem wreath_engelComm_r (x : Wreath n) :
    engelComm x ⟨0, DihedralGroup.r 1⟩ (2 + 2 ^ n) = 1 := by
  have hdi : (engelComm x ⟨0, DihedralGroup.r 1⟩ 2).toDihedral = 1 := by
    rw [engelComm_toDihedral, dihedral_engelComm_r_one]
  have hy : engelComm x ⟨0, DihedralGroup.r 1⟩ 2 =
      ⟨(engelComm x ⟨0, DihedralGroup.r 1⟩ 2).toFun, 1⟩ :=
    Wreath.ext rfl hdi
  rw [engelComm_add, hy, engelComm_wreath_eq_diffOp_iterate, diffOp_iterate_pow_eq_zero]
  rfl

/-! ### The binomial lower bound for the translation -/

/-- The function supported at `0` with value `1`. -/
private def wreathSingle (n : ℕ) : ZMod (2 ^ n) → ZMod 2 :=
  fun x => if x = 0 then 1 else 0

private theorem diffOp_r_apply (b : ZMod (2 ^ n) → ZMod 2) (x : ZMod (2 ^ n)) :
    diffOp n (DihedralGroup.r 1) b x = b (x + 1) - b x := by
  simp [diffOp, wreathSmul, dihedralAct]

private theorem diffOp_iterate_single :
    ∀ k : ℕ, k < 2 ^ n → ∀ j : ℕ, j < 2 ^ n →
      (diffOp n (DihedralGroup.r 1))^[k] (wreathSingle n) (-(j : ZMod (2 ^ n))) =
        if j ≤ k then (Nat.choose k j : ZMod 2) else 0 := by
  intro k
  induction k with
  | zero =>
    intro _ j hj
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · simp [wreathSingle]
    · have hne : (-(j : ZMod (2 ^ n))) ≠ 0 := by
        rw [ne_eq, neg_eq_zero]
        intro hzero
        have hval := congrArg ZMod.val hzero
        simp only [ZMod.val_natCast, Nat.mod_eq_of_lt hj, ZMod.val_zero] at hval
        omega
      simp only [Function.iterate_zero_apply, wreathSingle]
      rw [ite_eq_right hne, ite_eq_right (by omega : ¬ j ≤ 0)]
  | succ k ih =>
    intro hk j hj
    have hk' : k < 2 ^ n := by omega
    have ih' := ih hk'
    rw [Function.iterate_succ_apply', diffOp_r_apply]
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · have hpt : (1 : ZMod (2 ^ n)) = -(((2 ^ n - 1 : ℕ)) : ZMod (2 ^ n)) := by
        have h2n : ((2 ^ n : ℕ) : ZMod (2 ^ n)) = 0 := ZMod.natCast_self _
        have hcast : (((2 ^ n - 1 : ℕ)) : ZMod (2 ^ n)) + 1 = 0 := by
          rw [Nat.cast_sub (by omega : 1 ≤ 2 ^ n), ZMod.natCast_self, Nat.cast_one,
            zero_sub, neg_add_cancel]
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hcast
      have h1 : (-((0 : ℕ) : ZMod (2 ^ n)) + 1) = 1 := by simp
      have h1' : (diffOp n (DihedralGroup.r 1))^[k] (wreathSingle n) (1 : ZMod (2 ^ n)) =
          (diffOp n (DihedralGroup.r 1))^[k] (wreathSingle n)
            (-(((2 ^ n - 1 : ℕ)) : ZMod (2 ^ n))) := by
        rw [hpt]
      rw [h1, h1', ih' (2 ^ n - 1) (by omega), ite_eq_right (by omega : ¬ 2 ^ n - 1 ≤ k),
        ih' 0 (by omega)]
      rw [ite_eq_left (Nat.zero_le _), Nat.choose_zero_right, ite_eq_left (Nat.zero_le _),
        Nat.choose_zero_right]
      decide
    · have hpt : -(j : ZMod (2 ^ n)) + 1 = -(((j - 1 : ℕ)) : ZMod (2 ^ n)) := by
        rw [Nat.cast_sub hjpos, Nat.cast_one]
        ring
      rw [hpt, ih' (j - 1) (by omega), ih' j hj]
      by_cases hjk : j ≤ k
      · rw [ite_eq_left (by omega : j - 1 ≤ k), ite_eq_left hjk,
          ite_eq_left (by omega : j ≤ k + 1)]
        have hpas : Nat.choose (k + 1) j = Nat.choose k (j - 1) + Nat.choose k j := by
          obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
          simp [Nat.choose_succ_succ]
        rw [hpas, Nat.cast_add]
        have hneg : ∀ u : ZMod 2, -u = u := by decide
        rw [sub_eq_add_neg, hneg]
      · rcases Nat.eq_or_lt_of_le (by omega : k + 1 ≤ j) with hjeq | hjgt
        · subst hjeq
          rw [ite_eq_left (by omega : k + 1 - 1 ≤ k), ite_eq_right (by omega : ¬ k + 1 ≤ k),
            ite_eq_left (le_refl _), Nat.add_sub_cancel]
          simp [Nat.choose_self]
        · rw [ite_eq_right (by omega : ¬ j - 1 ≤ k), ite_eq_right (by omega : ¬ j ≤ k),
            ite_eq_right (by omega : ¬ j ≤ k + 1)]
          simp

private theorem diffOp_iterate_single_ne_zero {k : ℕ} (hk : k < 2 ^ n) :
    (diffOp n (DihedralGroup.r 1))^[k] (wreathSingle n) ≠ 0 := by
  intro hzero
  have h0 := congrFun hzero 0
  simp only [Pi.zero_apply] at h0
  have hformula := diffOp_iterate_single k hk 0 (pow_pos (by norm_num : (0:ℕ) < 2) n)
  rw [Nat.cast_zero, neg_zero] at hformula
  rw [hformula] at h0
  simp at h0

/-! ### The counterexample group -/

/-- The element supported at coordinate `m`, equal to the reflection `sr 0` there. -/
private def prodU (m : ℕ) : ∀ n : ℕ, Wreath n :=
  Function.update 1 m ⟨0, DihedralGroup.sr 0⟩

/-- The element supported at coordinate `m`, equal to the reflection `sr 1` there. -/
private def prodV (m : ℕ) : ∀ n : ℕ, Wreath n :=
  Function.update 1 m ⟨0, DihedralGroup.sr 1⟩

/-- The element supported at coordinate `m`, equal to the translation `r 1` there. -/
private def prodB (m : ℕ) : ∀ n : ℕ, Wreath n :=
  Function.update 1 m ⟨0, DihedralGroup.r 1⟩

private theorem prodU_apply_self (m : ℕ) :
    prodU m m = (⟨0, DihedralGroup.sr 0⟩ : Wreath m) :=
  Function.update_self _ _ _

private theorem prodV_apply_self (m : ℕ) :
    prodV m m = (⟨0, DihedralGroup.sr 1⟩ : Wreath m) :=
  Function.update_self _ _ _

private theorem prodB_apply_self (m : ℕ) :
    prodB m m = (⟨0, DihedralGroup.r 1⟩ : Wreath m) :=
  Function.update_self _ _ _

private theorem prodU_apply_of_ne {m n : ℕ} (h : n ≠ m) : prodU m n = 1 :=
  Function.update_of_ne h _ _

private theorem prodV_apply_of_ne {m n : ℕ} (h : n ≠ m) : prodV m n = 1 :=
  Function.update_of_ne h _ _

private theorem prodB_apply_of_ne {m n : ℕ} (h : n ≠ m) : prodB m n = 1 :=
  Function.update_of_ne h _ _

private theorem prodU_mul_prodV (m : ℕ) : prodU m * prodV m = prodB m := by
  funext n
  by_cases h : n = m
  · subst n
    rw [Pi.mul_apply, prodU_apply_self, prodV_apply_self, prodB_apply_self]
    apply Wreath.ext
    · simp [wreath_mul_toFun, wreathSmul_zero]
    · simp [wreath_mul_toDihedral, DihedralGroup.sr_mul_sr]
  · rw [Pi.mul_apply, prodU_apply_of_ne h, prodV_apply_of_ne h, prodB_apply_of_ne h,
      mul_one]

private theorem engelComm_prodU (m : ℕ) (hm : 1 ≤ m) (h : ∀ n : ℕ, Wreath n) :
    engelComm h (prodU m) (m + 2) = 1 := by
  funext n
  simp only [Pi.one_apply]
  by_cases hnm : n = m
  · subst n
    rw [engelComm_pi_apply, prodU_apply_self]
    exact wreath_engelComm_sr hm 0 _
  · rw [engelComm_pi_apply, prodU_apply_of_ne hnm]
    exact engelComm_one_succ (h n) (m + 1)

private theorem engelComm_prodV (m : ℕ) (hm : 1 ≤ m) (h : ∀ n : ℕ, Wreath n) :
    engelComm h (prodV m) (m + 2) = 1 := by
  funext n
  simp only [Pi.one_apply]
  by_cases hnm : n = m
  · subst n
    rw [engelComm_pi_apply, prodV_apply_self]
    exact wreath_engelComm_sr hm 1 _
  · rw [engelComm_pi_apply, prodV_apply_of_ne hnm]
    exact engelComm_one_succ (h n) (m + 1)

private theorem engelComm_prodB (m : ℕ) (h : ∀ n : ℕ, Wreath n) :
    engelComm h (prodB m) (2 + 2 ^ m) = 1 := by
  funext n
  simp only [Pi.one_apply]
  by_cases hnm : n = m
  · subst n
    rw [engelComm_pi_apply, prodB_apply_self]
    exact wreath_engelComm_r _
  · rw [engelComm_pi_apply, prodB_apply_of_ne hnm,
      show (2 : ℕ) + 2 ^ m = 2 ^ m + 1 + 1 from by omega]
    exact engelComm_one_succ (h n) (2 ^ m + 1)

private theorem isEngel_prodU (m : ℕ) (hm : 1 ≤ m) : IsEngel (prodU m) :=
  ⟨m + 2, by omega, engelComm_prodU m hm⟩

private theorem isEngel_prodV (m : ℕ) (hm : 1 ≤ m) : IsEngel (prodV m) :=
  ⟨m + 2, by omega, engelComm_prodV m hm⟩

private theorem isEngel_prodB (m : ℕ) : IsEngel (prodB m) :=
  ⟨2 + 2 ^ m, by have hpos : 0 < 2 ^ m := pow_pos (by norm_num) m; omega,
    engelComm_prodB m⟩

private theorem engelLength_prodU_le (m : ℕ) (hm : 1 ≤ m) :
    engelLength (prodU m) ≤ m + 2 :=
  Nat.sInf_le ⟨by omega, engelComm_prodU m hm⟩

private theorem engelLength_prodV_le (m : ℕ) (hm : 1 ≤ m) :
    engelLength (prodV m) ≤ m + 2 :=
  Nat.sInf_le ⟨by omega, engelComm_prodV m hm⟩

private theorem engelLength_prodB_ge (m : ℕ) : 2 ^ m ≤ engelLength (prodB m) := by
  by_contra hcon
  have hKlt : engelLength (prodB m) < 2 ^ m := lt_of_not_ge hcon
  obtain ⟨l, hl1, hl2⟩ := isEngel_prodB m
  have hmem : engelLength (prodB m) ∈
      {l | 1 ≤ l ∧ ∀ h : ∀ n : ℕ, Wreath n, engelComm h (prodB m) l = 1} :=
    Nat.sInf_mem ⟨l, hl1, hl2⟩
  have hall := hmem.2 (Function.update (1 : ∀ n : ℕ, Wreath n) m ⟨wreathSingle m, 1⟩)
  have hcoord := congrFun hall m
  simp only [Pi.one_apply] at hcoord
  rw [engelComm_pi_apply] at hcoord
  have hup : Function.update (1 : ∀ n : ℕ, Wreath n) m ⟨wreathSingle m, 1⟩ m =
      (⟨wreathSingle m, 1⟩ : Wreath m) :=
    Function.update_self _ _ _
  rw [hup, prodB_apply_self, engelComm_wreath_eq_diffOp_iterate] at hcoord
  have hne := diffOp_iterate_single_ne_zero hKlt
  apply hne
  have hfun := congrArg Wreath.toFun hcoord
  simpa only [wreath_one_toFun] using hfun

/-! ### Polynomial growth -/

private theorem eval_mono {φ : MvPolynomial (Fin 2) ℕ} {x y : Fin 2 → ℕ}
    (h : ∀ i, x i ≤ y i) : MvPolynomial.eval x φ ≤ MvPolynomial.eval y φ := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq']
  apply Finset.sum_le_sum
  intro s _
  apply Nat.mul_le_mul_left
  apply Finset.prod_le_prod
  intro i _
  exact Nat.pow_le_pow_left (h i) _

private theorem eval_le_bound (φ : MvPolynomial (Fin 2) ℕ) (M : ℕ) (hM : 1 ≤ M)
    (x : Fin 2 → ℕ) (hx : ∀ i, x i ≤ M) :
    MvPolynomial.eval x φ ≤ (∑ s ∈ φ.support, φ.coeff s) * M ^ φ.totalDegree := by
  calc MvPolynomial.eval x φ
      = ∑ s ∈ φ.support, φ.coeff s * ∏ i, x i ^ s i := MvPolynomial.eval_eq' _ _
    _ ≤ ∑ s ∈ φ.support, φ.coeff s * M ^ φ.totalDegree := by
        apply Finset.sum_le_sum
        intro s hs
        have hsum : (∑ i, s i) = s.sum (fun _ e => e) := by
          rw [Finsupp.sum_fintype _ _ (fun i => rfl)]
        have hprod : ∏ i, x i ^ s i ≤ M ^ φ.totalDegree := by
          calc ∏ i, x i ^ s i ≤ ∏ i, M ^ s i :=
                Finset.prod_le_prod (fun i _ => Nat.pow_le_pow_left (hx i) _)
            _ = M ^ (∑ i, s i) := Finset.prod_pow_eq_pow_sum _ _ _
            _ = M ^ (s.sum fun _ e => e) := by rw [hsum]
            _ ≤ M ^ φ.totalDegree :=
                pow_le_pow_right₀ hM (MvPolynomial.le_totalDegree hs)
        exact Nat.mul_le_mul_left _ hprod
    _ = (∑ s ∈ φ.support, φ.coeff s) * M ^ φ.totalDegree := (Finset.sum_mul _ _ _).symm

private theorem two_pow_gt_sq {m : ℕ} (hm : 6 ≤ m) : (m + 1) ^ 2 < 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    have h1 : 2 * k + 3 ≤ (k + 1) ^ 2 := by nlinarith
    calc (k + 1 + 1) ^ 2 = (k + 1) ^ 2 + (2 * k + 3) := by ring
      _ < 2 ^ k + 2 ^ k := by linarith
      _ = 2 ^ (k + 1) := by rw [pow_succ, mul_two]

private theorem exists_pow_gt_mul (C : ℕ) : ∃ m : ℕ, C * (m + 1) < 2 ^ m := by
  obtain ⟨m, hm6, hmC⟩ : ∃ m, 6 ≤ m ∧ C ≤ m := ⟨max 6 C, le_max_left _ _, le_max_right _ _⟩
  refine ⟨m, ?_⟩
  calc C * (m + 1) ≤ m * (m + 1) := Nat.mul_le_mul_right _ hmC
    _ < (m + 1) ^ 2 := by
        rw [pow_two]
        exact mul_lt_mul_of_pos_right (by omega) (by omega)
    _ < 2 ^ m := two_pow_gt_sq hm6

private theorem exists_pow_gt_mul_pow (S D : ℕ) (hD : 1 ≤ D) :
    ∃ n : ℕ, 2 ≤ n ∧ S * (n + 3) ^ D < 2 ^ n := by
  obtain ⟨m0, hm0⟩ := exists_pow_gt_mul (S * (D + 3))
  have hm : S * (D + 3) * (m0 + 2 + 1) < 2 ^ (m0 + 2) := by
    calc S * (D + 3) * (m0 + 2 + 1)
        = (S * (D + 3)) * (m0 + 2 + 1) := by ring
      _ ≤ (S * (D + 3)) * (4 * (m0 + 1)) :=
          Nat.mul_le_mul_left _ (by omega)
      _ = 4 * (S * (D + 3) * (m0 + 1)) := by ring
      _ < 4 * 2 ^ m0 := mul_lt_mul_of_pos_left hm0 (by norm_num)
      _ = 2 ^ (m0 + 2) := by rw [pow_add]; ring
  refine ⟨(m0 + 2) * D, ?_, ?_⟩
  · calc 2 ≤ m0 + 2 := by omega
      _ ≤ (m0 + 2) * D := Nat.le_mul_of_pos_right _ (by omega)
  · have hle1 : (m0 + 2) * D + 3 ≤ (D + 3) * (m0 + 2 + 1) := by nlinarith
    calc S * ((m0 + 2) * D + 3) ^ D
        ≤ S * ((D + 3) * (m0 + 2 + 1)) ^ D := by
          apply Nat.mul_le_mul_left
          exact Nat.pow_le_pow_left hle1 _
      _ = S * ((D + 3) ^ D * (m0 + 2 + 1) ^ D) := by rw [Nat.mul_pow]
      _ ≤ (S * (D + 3) * (m0 + 2 + 1)) ^ D := by
          have hSD : S ≤ S ^ D := Nat.le_self_pow (by omega : D ≠ 0) S
          rw [Nat.mul_pow, Nat.mul_pow]
          calc S * ((D + 3) ^ D * (m0 + 2 + 1) ^ D)
              = (S * (D + 3) ^ D) * (m0 + 2 + 1) ^ D := by ring
            _ ≤ (S ^ D * (D + 3) ^ D) * (m0 + 2 + 1) ^ D :=
                Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hSD)
      _ < (2 ^ (m0 + 2)) ^ D :=
          pow_lt_pow_left₀ hm (Nat.zero_le _) (by omega : D ≠ 0)
      _ = 2 ^ ((m0 + 2) * D) := by rw [← pow_mul]

private theorem exists_eval_lt_pow (φ : MvPolynomial (Fin 2) ℕ) :
    ∃ n : ℕ, 2 ≤ n ∧ MvPolynomial.eval ![n + 2, n + 2] φ < 2 ^ n := by
  rcases Nat.eq_zero_or_pos (∑ s ∈ φ.support, φ.coeff s) with hS0 | hSpos
  · refine ⟨2, le_refl 2, ?_⟩
    have hb := eval_le_bound φ 5 (by norm_num) ![2 + 2, 2 + 2]
      (by intro i; fin_cases i <;> simp)
    rw [hS0, zero_mul] at hb
    have h0 : MvPolynomial.eval ![2 + 2, 2 + 2] φ = 0 := Nat.le_zero.mp hb
    rw [h0]
    norm_num
  · rcases Nat.eq_zero_or_pos φ.totalDegree with hD0 | hDpos
    · obtain ⟨m, hm⟩ := exists_pow_gt_mul (∑ s ∈ φ.support, φ.coeff s)
      refine ⟨max m 2, le_max_right _ _, ?_⟩
      have hb := eval_le_bound φ (max m 2 + 3) (by omega) ![max m 2 + 2, max m 2 + 2]
        (by intro i; fin_cases i <;> simp)
      rw [hD0, pow_zero, mul_one] at hb
      have hSle : (∑ s ∈ φ.support, φ.coeff s) ≤
          (∑ s ∈ φ.support, φ.coeff s) * (m + 1) := by
        calc (∑ s ∈ φ.support, φ.coeff s)
            = (∑ s ∈ φ.support, φ.coeff s) * 1 := (mul_one _).symm
          _ ≤ (∑ s ∈ φ.support, φ.coeff s) * (m + 1) :=
              Nat.mul_le_mul_left _ (by omega)
      have hpow : (2 : ℕ) ^ m ≤ 2 ^ max m 2 :=
        pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
      omega
    · obtain ⟨n, hn2, hnlt⟩ := exists_pow_gt_mul_pow (∑ s ∈ φ.support, φ.coeff s)
        φ.totalDegree hDpos
      refine ⟨n, hn2, ?_⟩
      have hb := eval_le_bound φ (n + 3) (by omega) ![n + 2, n + 2]
        (by intro i; fin_cases i <;> simp)
      omega

/--
**Engel lengths of products admit no polynomial bound (Kourovka 11.88).** There is a group $G$
such that for every polynomial $\varphi(x, y)$ in two variables with natural-number coefficients
there are $u, v \in G$ such that $u$, $v$ and $uv$ are Engel elements and
$l(uv) > \varphi(l(u), l(v))$. Here $g \in G$ is an Engel element if there is a $k \ge 1$ with
$[h, g; k] = 1$ for all $h \in G$, and its Engel length $l(g)$ is the least such $k$, where
$[h, g; 0] = h$, $[h, g; i + 1] = [[h, g; i], g]$ and $[x, y] = x^{-1} y^{-1} x y$.

For a prime $p$, Dolbak builds finite $p$-groups $G_n$ (wreath products of a cyclic group of
order $p$ by groups $K_n$) with elements $c_n$ and $c_n^{-1} b_0$ of Engel length at most
$(n + 1)p - n + 1$ whose product $b_0$ has Engel length at least $p^n$. He takes the direct
product of the $G_n$ in the restricted sense (the direct sum, whose elements have finite support).
It is a single Engel group: an element of finite support has Engel length at most the largest
Engel length of its coordinates, and each $G_n$ is a finite $p$-group, hence nilpotent. (The
unrestricted product is not Engel: the element with $b_0$ in every coordinate has unbounded Engel
length.) Let $u_n$ and $v_n$ be $c_n$ and $c_n^{-1} b_0$ in coordinate $n$ and $1$ elsewhere: they
are Engel elements of length at most $(n + 1)p - n + 1$, and $u_n v_n$ has length at least $p^n$,
which exceeds every polynomial in the lengths of the factors (Theorem 1: there are Engel groups in
which the Engel length of a product of two elements is bounded by no polynomial in the Engel
lengths of the factors). The refutation of this statement uses only that $u_n$, $v_n$ and
$u_n v_n$ are Engel elements of one group. The Kourovka Archive answers 11.88 "No, it does not".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 11.88 (V. A.
Roman'kov); resolution: L. V. Dolbak, The Engel length of the product of Engel elements, Siberian
Math. J. 47, no. 1 (2006), 55-57, Theorem 1 and its proof; Kourovka Archive, Problem 11.88: "No,
it does not", https://doi.org/10.1007/s11202-006-0006-9.
-/
theorem engelLengthPolynomialBound_refuted : ¬ engelLengthPolynomialBound := by
  intro hb
  obtain ⟨φ, hφ⟩ := hb (∀ n : ℕ, Wreath n)
  obtain ⟨n, hn2, hnlt⟩ := exists_eval_lt_pow φ
  have hle := hφ (prodU n) (prodV n) (isEngel_prodU n (by omega))
    (isEngel_prodV n (by omega)) (by rw [prodU_mul_prodV]; exact isEngel_prodB n)
  rw [prodU_mul_prodV] at hle
  have hmono : MvPolynomial.eval ![engelLength (prodU n), engelLength (prodV n)] φ ≤
      MvPolynomial.eval ![n + 2, n + 2] φ := by
    apply eval_mono
    intro i
    fin_cases i
    · simpa using engelLength_prodU_le n (by omega : 1 ≤ n)
    · simpa using engelLength_prodV_le n (by omega : 1 ≤ n)
  have hge := engelLength_prodB_ge n
  omega

end MathlibExt.GroupTheory.EngelElementLengthPolynomialKourovka11Problem88Wanted
