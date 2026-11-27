/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.FinitelyPresentedGroup
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite presentability in the torsion-free quasivariety (Kourovka Notebook Problem 18.17)

Kourovka Notebook, Archive of Solved Problems, Problem 18.17 (O. V. Belegradek): is there a
torsion-free group which is finitely presented in the quasivariety of torsion-free groups but not
finitely presentable in the variety of all groups?

This file proves Budkin's existence theorem using the root closure of finitely many relators.
Successive commutators become trivial in the torsion-free quotient. Their images in a
triangular matrix group obstruct finite normal generation of the relation subgroup.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.17 (O. V.
Belegradek). UnsolvedMath record UM-00701446 (`KOU-18.17`), dataset ulamai/UnsolvedMath v1.8.0.

In a quasivariety `𝔎` the group presented by `⟨X | S⟩` is `F(X) ⧸ R`, with `R` the intersection of
all normal `N ⊇ S` with `F(X) ⧸ N ∈ 𝔎`. For torsion-free groups `F(X) ⧸ N` is torsion-free exactly
when `xᵏ ∈ N, k ≥ 1` implies `x ∈ N`, so `R` is the least such normal subgroup containing `S`.
Finitely presented in `𝔎` means `X` and `S` finite; the presentation is given by a surjection from
`FreeGroup (Fin n)` with kernel `R`. Finite presentability in the variety of all groups is Mathlib's
`Group.IsFinitelyPresented`.
-/

namespace MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17Wanted

@[expose] public section

/-- **Relation subgroup of a torsion-free presentation.** Let $n$ be a natural number, let $F_n$ be
the free group on the $n$ letters $0, 1, \dots, n - 1$, and let $S$ be a subset of $F_n$. The
relation subgroup of $S$ in the quasivariety of torsion-free groups is the intersection of all
normal subgroups $N$ of $F_n$ that contain $S$ and satisfy the following: for every $x \in F_n$
and every integer $k \ge 1$, if $x^k \in N$ then $x \in N$. Equivalently, it is the least normal
subgroup $N$ of $F_n$ containing $S$ for which $F_n / N$ is torsion-free. -/
def torsionFreeRelations {n : ℕ} (S : Set (FreeGroup (Fin n))) : Subgroup (FreeGroup (Fin n)) :=
  sInf {N | N.Normal ∧ S ⊆ N ∧ ∀ (x : FreeGroup (Fin n)) (k : ℕ), 0 < k → x ^ k ∈ N → x ∈ N}

/-- **Groups finitely presented in the torsion-free quasivariety.** A group $G$ is finitely
presented in the quasivariety of torsion-free groups if there are a natural number $n$, a finite
subset $S$ of the free group $F_n$ on $n$ letters, and a surjective homomorphism
$f \colon F_n \to G$ whose kernel is the relation subgroup of $S$ in the quasivariety of
torsion-free groups. -/
def IsTorsionFreeFinitelyPresented (G : Type) [Group G] : Prop :=
  ∃ (n : ℕ) (S : Finset (FreeGroup (Fin n))) (f : FreeGroup (Fin n) →* G),
    Function.Surjective f ∧ f.ker = torsionFreeRelations (S : Set (FreeGroup (Fin n)))

/-- **Kourovka Problem 18.17 (statement).** The statement that there is a torsion-free group $G$ (no
element of $G$ other than the identity has finite order) that is finitely presented in the
quasivariety of torsion-free groups but is not a finitely presented group.

The problem was posed by O. V. Belegradek. -/
def torsionFreePresentedNotFinitelyPresented : Prop :=
  ∃ (G : Type) (_ : Group G), (∀ g : G, g ≠ 1 → ¬ IsOfFinOrder g) ∧
    IsTorsionFreeFinitelyPresented G ∧ ¬ Group.IsFinitelyPresented G

end

open scoped commutatorElement

private structure Generators (G : Type*) where
  a : G
  b : G
  c : G
  d : G
  e : G
  t : G
  s : G

private def Generators.map {G H : Type*} (f : G → H) (x : Generators G) : Generators H :=
  ⟨f x.a, f x.b, f x.c, f x.d, f x.e, f x.t, f x.s⟩

-- The commutation and conjugation relations used to propagate square roots.
private def Generators.structuralRelators {G : Type*} [Group G] (x : Generators G) : List G :=
  [⁅x.t, x.s⁆, ⁅x.t, x.a⁆, ⁅x.t, x.e⁆, ⁅x.s, x.c⁆, ⁅x.s, x.d⁆,
    MulAut.conj x.s x.b / MulAut.conj x.t⁻¹ x.b,
    MulAut.conj x.t x.d / x.d ^ 2, ⁅x.a, x.b⁆ / x.d,
    MulAut.conj x.b x.c / (x.c * x.e),
    ⁅x.a, x.d⁆, ⁅x.a, x.c⁆, ⁅x.b, x.d⁆, ⁅x.d, x.e⁆]

private theorem Generators.map_structuralRelators {G H : Type*} [Group G] [Group H]
    (x : Generators G) (f : G →* H) :
    x.structuralRelators.map f = (x.map f).structuralRelators := by
  simp [Generators.structuralRelators, Generators.map, MulAut.conj_apply]

private def Generators.rootWord {G : Type*} [Group G] (x : Generators G) (n : ℕ) : G :=
  ⁅(MulAut.conj x.t⁻¹ ^ n) x.d, x.c⁆

private theorem Generators.map_rootWord {G H : Type*} [Group G] [Group H]
    (x : Generators G) (f : G →* H) (n : ℕ) : f (x.rootWord n) = (x.map f).rootWord n := by
  simp [Generators.rootWord, Generators.map, ← map_pow]

private theorem conj_eq_self_of_commute {G : Type*} [Group G] {x y : G} (h : Commute x y) :
    MulAut.conj x y = y := by rw [conj_eq_commutatorElement_mul, h.commutator_eq, one_mul]

private theorem Generators.rootWord_sq {G : Type*} [Group G] (x : Generators G)
    (h : ∀ w ∈ x.structuralRelators, w = 1) (n : ℕ) :
    x.rootWord (n + 1) ^ 2 = x.rootWord n := by
  simp only [Generators.structuralRelators, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, commutatorElement_eq_one_iff_commute] at h
  obtain ⟨hts, hta, hte, hsc, hsd, hb, htd, hab, hbc, had, hac, hbd, hde⟩ := h
  let u : MulAut G := MulAut.conj x.t⁻¹
  let v := MulAut.conj x.s
  have huv : Commute u v := hts.inv_left.map MulAut.conj
  have hu_a (k : ℕ) : (u ^ k) x.a = x.a := by
    rw [show u = MulAut.conj _ from rfl, ← map_pow]
    exact conj_eq_self_of_commute (hta.inv_left.pow_left k)
  have hu_e (k : ℕ) : (u ^ k) x.e = x.e := by
    rw [show u = MulAut.conj _ from rfl, ← map_pow]
    exact conj_eq_self_of_commute (hte.inv_left.pow_left k)
  have hv_c (k : ℕ) : (v ^ k) x.c = x.c := by
    rw [show v = MulAut.conj _ from rfl, ← map_pow]
    exact conj_eq_self_of_commute (hsc.pow_left k)
  have hv_d (k : ℕ) : (v ^ k) x.d = x.d := by
    rw [show v = MulAut.conj _ from rfl, ← map_pow]
    exact conj_eq_self_of_commute (hsd.pow_left k)
  have hu_b (k : ℕ) : (u ^ k) x.b = (v ^ k) x.b := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ u, MulAut.mul_apply, ← show v x.b = u x.b from div_eq_one.mp hb,
        ← MulAut.mul_apply, (huv.pow_left k).eq, MulAut.mul_apply, ih, ← MulAut.mul_apply,
        ← pow_succ']
  have hu_d : u (x.d ^ 2) = x.d := by
    rw [← div_eq_one.mp htd]
    simp [u, MulAut.conj_apply, ← mul_assoc]
  have hdstep (k : ℕ) : ((u ^ (k + 1)) x.d) ^ 2 = (u ^ k) x.d := by
    rw [← map_pow, pow_succ, MulAut.mul_apply, hu_d]
  -- The displaced commutator commutes with both factors generating its first argument.
  have hcentral (k : ℕ) : Commute ((u ^ k) x.d) ⁅(u ^ k) x.d, x.c⁆ := by
    let dk := (u ^ k) x.d
    let bk := (u ^ k) x.b
    let ek := (v ^ k) x.e
    have had' : Commute x.a dk := by simpa only [hu_a] using had.map (u ^ k)
    have hbd' : Commute bk dk := hbd.map (u ^ k)
    have hde' : Commute dk ek := by
      have h' : Commute x.d ek := by simpa only [hv_d] using hde.map (v ^ k)
      have hu_ek : (u ^ k) ek = ek := by
        change (u ^ k) ((v ^ k) x.e) = _
        rw [← MulAut.mul_apply, ((huv.pow_left k).pow_right k).eq, MulAut.mul_apply, hu_e]
      simpa only [hu_ek] using h'.map (u ^ k)
    have hab' : ⁅x.a, bk⁆ = dk := by
      simpa only [map_commutatorElement, hu_a] using congrArg (u ^ k) (div_eq_one.mp hab)
    have hbc' : MulAut.conj bk x.c = x.c * ek := by
      change MulAut.conj ((u ^ k) x.b) x.c = _
      rw [hu_b]
      simpa only [MulAut.conj_apply, map_mul, map_inv, hv_c] using
        congrArg (v ^ k) (div_eq_one.mp hbc)
    have ha : Commute x.a ⁅dk, x.c⁆ :=
      ((had'.mul_right hac).mul_right had'.inv_right).mul_right hac.inv_right
    have hb' : Commute bk ⁅dk, x.c⁆ := by
      have hfix : MulAut.conj bk ⁅dk, x.c⁆ = ⁅dk, x.c⁆ := by
        rw [map_commutatorElement, conj_eq_self_of_commute hbd', hbc',
          commutatorElement_mul_right_eq_mul_conj, hde'.commutator_eq, mul_one,
          mul_inv_cancel_right]
      rw [conj_eq_commutatorElement_mul] at hfix
      exact commutatorElement_eq_one_iff_commute.mp
        (mul_right_cancel (hfix.trans (one_mul _).symm))
    change Commute dk ⁅dk, x.c⁆
    rw [← hab']
    have hh : Commute ⁅x.a, bk⁆ ⁅dk, x.c⁆ :=
      ((ha.mul_left hb').mul_left ha.inv_left).mul_left hb'.inv_left
    simpa only [hab'] using hh
  change ⁅(u ^ (n + 1)) x.d, x.c⁆ ^ 2 = ⁅(u ^ n) x.d, x.c⁆
  rw [(hcentral (n + 1)).commutatorElement_pow_left, hdstep]

-- These coordinates describe the matrix [[1,a,f,z],[0,d,b,g],[0,0,e,c],[0,0,0,1]].
-- The two variable diagonal entries are positive.
@[ext] private structure Triangular where
  d : ℚ
  e : ℚ
  a : ℚ
  b : ℚ
  c : ℚ
  f : ℚ
  g : ℚ
  z : ℚ
  d_pos : 0 < d
  e_pos : 0 < e

private def Triangular.mul (x y : Triangular) : Triangular where
  d := x.d * y.d
  e := x.e * y.e
  a := y.a + x.a * y.d
  b := x.d * y.b + x.b * y.e
  c := x.e * y.c + x.c
  f := y.f + x.a * y.b + x.f * y.e
  g := x.d * y.g + x.b * y.c + x.g
  z := y.z + x.a * y.g + x.f * y.c + x.z
  d_pos := mul_pos x.d_pos y.d_pos
  e_pos := mul_pos x.e_pos y.e_pos

private def Triangular.inv (x : Triangular) : Triangular where
  d := x.d⁻¹
  e := x.e⁻¹
  a := -x.a / x.d
  b := -x.b / (x.d * x.e)
  c := -x.c / x.e
  f := (x.a * x.b - x.f * x.d) / (x.d * x.e)
  g := (x.b * x.c - x.g * x.e) / (x.d * x.e)
  z := -x.z - x.a * ((x.b * x.c - x.g * x.e) / (x.d * x.e)) - x.f * (-x.c / x.e)
  d_pos := inv_pos.mpr x.d_pos
  e_pos := inv_pos.mpr x.e_pos

private def Triangular.one : Triangular :=
  ⟨1, 1, 0, 0, 0, 0, 0, 0, zero_lt_one, zero_lt_one⟩

private instance triangularGroup : Group Triangular where
  mul := Triangular.mul
  inv := Triangular.inv
  one := Triangular.one
  mul_assoc x y z := by
    change (x.mul y).mul z = x.mul (y.mul z)
    apply Triangular.ext <;> dsimp [Triangular.mul] <;> ring
  one_mul x := by
    change Triangular.one.mul x = x
    apply Triangular.ext <;> simp [Triangular.mul, Triangular.one]
  mul_one x := by
    change x.mul Triangular.one = x
    apply Triangular.ext <;> simp [Triangular.mul, Triangular.one]
  inv_mul_cancel x := by
    have hd := ne_of_gt x.d_pos
    have he := ne_of_gt x.e_pos
    change x.inv.mul x = Triangular.one
    apply Triangular.ext <;> dsimp [Triangular.mul, Triangular.inv, Triangular.one] <;>
      field_simp [hd, he] <;> ring

private def shear (q : ℚ) : Triangular := { Triangular.one with z := q }

private theorem shear_zero : shear 0 = 1 := rfl

private theorem shear_mul (q r : ℚ) : shear q * shear r = shear (q + r) := by
  change (shear q).mul (shear r) = shear (q + r)
  apply Triangular.ext <;> simp [Triangular.mul, shear, Triangular.one, add_comm]

private theorem shear_inv (q : ℚ) : (shear q)⁻¹ = shear (-q) := by
  apply inv_eq_of_mul_eq_one_right
  rw [shear_mul, add_neg_cancel, shear_zero]

private theorem shear_commute (q : ℚ) (x : Triangular) : Commute (shear q) x := by
  change (shear q).mul x = x.mul (shear q)
  apply Triangular.ext <;> simp [Triangular.mul, shear, Triangular.one, add_comm]

private def shearSubgroup (A : AddSubgroup ℚ) : Subgroup Triangular where
  carrier := {x | ∃ q ∈ A, shear q = x}
  one_mem' := ⟨0, A.zero_mem, shear_zero⟩
  mul_mem' := by
    rintro _ _ ⟨q, hq, rfl⟩ ⟨r, hr, rfl⟩
    exact ⟨q + r, A.add_mem hq hr, (shear_mul _ _).symm⟩
  inv_mem' := by
    rintro _ ⟨q, hq, rfl⟩
    exact ⟨-q, A.neg_mem hq, (shear_inv _).symm⟩

private instance shearSubgroupNormal (A : AddSubgroup ℚ) : (shearSubgroup A).Normal where
  conj_mem := by
    rintro _ ⟨q, hq, rfl⟩ x
    exact ⟨q, hq, by rw [(shear_commute q x).symm.eq, mul_inv_cancel_right]⟩

private theorem shear_mem (A : AddSubgroup ℚ) (q : ℚ) : shear q ∈ shearSubgroup A ↔ q ∈ A := by
  constructor
  · rintro ⟨r, hr, he⟩
    simpa only [show r = q from congrArg Triangular.z he] using hr
  · intro h
    exact ⟨q, h, rfl⟩

private theorem diag_pow (x : Triangular) (n : ℕ) :
    (x ^ n).d = x.d ^ n ∧ (x ^ n).e = x.e ^ n := by
  induction n with
  | zero => simp [show (1 : Triangular) = Triangular.one from rfl, Triangular.one]
  | succ n ih =>
    rw [pow_succ x]
    change (x ^ n).d * x.d = x.d ^ (n + 1) ∧ (x ^ n).e * x.e = x.e ^ (n + 1)
    simp only [ih.1, ih.2, pow_succ, and_self]

private theorem firstSuperdiag_pow (x : Triangular) (hd : x.d = 1) (he : x.e = 1) (n : ℕ) :
    (x ^ n).a = n * x.a ∧ (x ^ n).b = n * x.b ∧ (x ^ n).c = n * x.c := by
  induction n with
  | zero => simp [show (1 : Triangular) = Triangular.one from rfl, Triangular.one]
  | succ n ih =>
    have h := diag_pow x n
    rw [pow_succ x]
    change (x.a + (x ^ n).a * x.d = _ ∧
      (x ^ n).d * x.b + (x ^ n).b * x.e = _ ∧ (x ^ n).e * x.c + (x ^ n).c = _)
    rw [ih.1, ih.2.1, ih.2.2, h.1, h.2, hd, he]
    push_cast
    simp only [one_pow, one_mul, mul_one]
    exact ⟨by ring, by ring, by ring⟩

private theorem secondSuperdiag_pow (x : Triangular) (hd : x.d = 1) (he : x.e = 1)
    (ha : x.a = 0) (hc : x.c = 0) (n : ℕ) :
    (x ^ n).f = n * x.f ∧ (x ^ n).g = n * x.g := by
  induction n with
  | zero => simp [show (1 : Triangular) = Triangular.one from rfl, Triangular.one]
  | succ n ih =>
    have h := diag_pow x n
    have h₁ := firstSuperdiag_pow x hd he n
    rw [pow_succ x]
    change (x.f + (x ^ n).a * x.b + (x ^ n).f * x.e = _ ∧
      (x ^ n).d * x.g + (x ^ n).b * x.c + (x ^ n).g = _)
    rw [ih.1, ih.2, h.1, h₁.1, hd, he, ha, hc]
    push_cast
    simp only [one_pow, one_mul, mul_one, mul_zero, zero_mul, add_zero]
    exact ⟨by ring, by ring⟩

-- If a positive power is a central shear, read off the diagonal, then the next two diagonals.
private theorem shear_root_closed (x : Triangular) (n : ℕ) (hn : 0 < n)
    (h : x ^ n ∈ shearSubgroup ⊤) : x ∈ shearSubgroup ⊤ := by
  obtain ⟨q, _, hq⟩ := h
  have hn' : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  obtain ⟨hd, he⟩ := diag_pow x n
  rw [← hq] at hd he
  have hd' : x.d = 1 := (pow_eq_one_iff_of_nonneg x.d_pos.le hn.ne').mp hd.symm
  have he' : x.e = 1 := (pow_eq_one_iff_of_nonneg x.e_pos.le hn.ne').mp he.symm
  obtain ⟨ha, hb, hc⟩ := firstSuperdiag_pow x hd' he' n
  rw [← hq] at ha hb hc
  have ha' : x.a = 0 := (mul_eq_zero.mp ha.symm).resolve_left hn'
  have hb' : x.b = 0 := (mul_eq_zero.mp hb.symm).resolve_left hn'
  have hc' : x.c = 0 := (mul_eq_zero.mp hc.symm).resolve_left hn'
  obtain ⟨hf, hg⟩ := secondSuperdiag_pow x hd' he' ha' hc' n
  rw [← hq] at hf hg
  have hf' : x.f = 0 := (mul_eq_zero.mp hf.symm).resolve_left hn'
  have hg' : x.g = 0 := (mul_eq_zero.mp hg.symm).resolve_left hn'
  exact ⟨x.z, trivial, Triangular.ext hd'.symm he'.symm ha'.symm hb'.symm hc'.symm
    hf'.symm hg'.symm rfl⟩

private theorem Triangular.mul_def (x y : Triangular) : x * y = x.mul y := rfl
private theorem Triangular.inv_def (x : Triangular) : x⁻¹ = x.inv := rfl
private theorem Triangular.one_def : (1 : Triangular) = Triangular.one := rfl

-- Elementary transvections in positions 12, 23, 34, 13 and 24, and two diagonal matrices.
private def matrixGenerators : Generators Triangular where
  a := { Triangular.one with a := 1 }
  b := { Triangular.one with b := 1 }
  c := { Triangular.one with c := 1 }
  d := { Triangular.one with f := 1 }
  e := { Triangular.one with g := 1 }
  t := { Triangular.one with e := 1 / 2, e_pos := by norm_num }
  s := { Triangular.one with d := 1 / 2, d_pos := by norm_num }

private theorem matrix_structuralRelators (w : Triangular)
    (hw : w ∈ matrixGenerators.structuralRelators) : w = 1 := by
  simp only [Generators.structuralRelators, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    try rw [div_eq_one]
    apply Triangular.ext <;>
      norm_num [matrixGenerators, commutatorElement_def, MulAut.conj_apply, pow_two,
        Triangular.mul_def, Triangular.inv_def, Triangular.one_def, Triangular.mul,
        Triangular.inv, Triangular.one] <;> rfl

private theorem matrix_rootWord (n : ℕ) :
    matrixGenerators.rootWord n = shear ((2 : ℚ) ^ n)⁻¹ := by
  induction n with
  | zero =>
    simp only [Generators.rootWord, pow_zero, MulAut.one_apply, inv_one]
    apply Triangular.ext <;>
      norm_num [matrixGenerators, shear, commutatorElement_def,
        Triangular.mul_def, Triangular.inv_def, Triangular.mul, Triangular.inv, Triangular.one]
  | succ n ih =>
    have hs := matrixGenerators.rootWord_sq matrix_structuralRelators n
    rw [ih] at hs
    obtain ⟨q, _, hq⟩ := shear_root_closed (matrixGenerators.rootWord (n + 1)) 2
      (by decide) (by rw [hs]; exact ⟨_, trivial, rfl⟩)
    rw [← hq] at hs ⊢
    rw [pow_two, shear_mul] at hs
    have hq' : q + q = ((2 : ℚ) ^ n)⁻¹ := congrArg Triangular.z hs
    congr 1
    rw [pow_succ, mul_inv, show (2 : ℚ)⁻¹ = 1 / 2 by norm_num]
    linarith

private def boundedDenominator (D : ℕ) : AddSubgroup ℚ where
  carrier := {q | ∃ z : ℤ, (D : ℚ) * q = z}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro q r ⟨z, hz⟩ ⟨w, hw⟩
    exact ⟨z + w, by rw [Int.cast_add, mul_add, hz, hw]⟩
  neg_mem' := by
    rintro q ⟨z, hz⟩
    exact ⟨-z, by rw [Int.cast_neg, mul_neg, hz]⟩

private theorem finite_subset_boundedDenominator {T : Set ℚ} (hT : T.Finite) :
    ∃ D : ℕ, 0 < D ∧ T ⊆ boundedDenominator D := by
  refine Set.Finite.induction_on T hT ?_ ?_
  · exact ⟨1, by decide, Set.empty_subset _⟩
  · intro q U _ _ hU
    obtain ⟨D, hD, hDU⟩ := hU
    refine ⟨q.den * D, Nat.mul_pos q.den_pos hD, ?_⟩
    intro r hr
    rcases Set.mem_insert_iff.mp hr with heq | hr
    · subst r
      refine ⟨(D : ℤ) * q.num, ?_⟩
      have h : (q.den : ℚ) * q = q.num := by
        conv_lhs =>
          arg 2
          rw [← q.num_div_den]
        field_simp
      push_cast
      rw [mul_comm (q.den : ℚ), mul_assoc, h, mul_comm]
    · obtain ⟨z, hz⟩ := hDU hr
      exact ⟨(q.den : ℤ) * z, by push_cast; rw [mul_assoc, hz]⟩

private theorem inverse_two_pow_not_mem (D : ℕ) (hD : 0 < D) :
    ((2 : ℚ) ^ D)⁻¹ ∉ boundedDenominator D := by
  rintro ⟨z, hz⟩
  have hp : 0 < (2 : ℚ) ^ D := by positivity
  have hlt : (D : ℚ) < (2 : ℚ) ^ D := by exact_mod_cast D.lt_two_pow_self
  have hz₀ : (0 : ℚ) < z := hz ▸ mul_pos (by exact_mod_cast hD) (inv_pos.mpr hp)
  have hz₁ : (z : ℚ) < 1 := by
    rw [← hz, ← div_eq_mul_inv]
    exact (div_lt_one hp).mpr hlt
  have hz₀' : 0 < z := by exact_mod_cast hz₀
  have hz₁' : z < 1 := by exact_mod_cast hz₁
  omega

-- Transfer a finite presentation to another finite generating set using lifts in both
-- directions. The correction relations identify each generator with its round trip.
private theorem finite_normal_kernel {α G : Type*} [Finite α] [Group G]
    (f : FreeGroup α →* G) (hf : Function.Surjective f) (hG : Group.IsFinitelyPresented G) :
    f.ker.IsFinitelyNormallyGenerated := by
  classical
  obtain ⟨n, g, hg, S, hS, hSker⟩ := hG.out
  let a : FreeGroup α →* FreeGroup (Fin n) :=
    FreeGroup.lift fun i => (hg (f (FreeGroup.of i))).choose
  let b : FreeGroup (Fin n) →* FreeGroup α :=
    FreeGroup.lift fun i => (hf (g (FreeGroup.of i))).choose
  have hga : g.comp a = f := by
    apply FreeGroup.ext_hom
    intro i
    simpa [a] using (hg (f (FreeGroup.of i))).choose_spec
  have hfb : f.comp b = g := by
    apply FreeGroup.ext_hom
    intro i
    simpa [b] using (hf (g (FreeGroup.of i))).choose_spec
  let correction (i : α) := FreeGroup.of i / b (a (FreeGroup.of i))
  let T := b '' S ∪ Set.range correction
  let N := Subgroup.normalClosure T
  refine ⟨T, (hS.image b).union (Set.finite_range correction), le_antisymm ?_ ?_⟩
  · apply Subgroup.normalClosure_le_normal
    rintro y (⟨s, hs, rfl⟩ | ⟨i, rfl⟩)
    · have hs' : s ∈ g.ker := hSker ▸ Subgroup.subset_normalClosure hs
      simpa [← hfb, MonoidHom.mem_ker] using hs'
    · have hb (x : FreeGroup (Fin n)) : f (b x) = g x := DFunLike.congr_fun hfb x
      have ha (x : FreeGroup α) : g (a x) = f x := DFunLike.congr_fun hga x
      simp [correction, hb, ha]
  · let q := QuotientGroup.mk' N
    have hq : q = (q.comp b).comp a := by
      apply FreeGroup.ext_hom
      intro i
      have hi : correction i ∈ N := Subgroup.subset_normalClosure (Or.inr ⟨i, rfl⟩)
      simpa [q, correction, ← QuotientGroup.eq_one_iff, div_eq_one] using hi
    have hgq : g.ker ≤ (q.comp b).ker := by
      rw [← hSker]
      apply Subgroup.normalClosure_le_normal
      intro s hs
      have hs' : b s ∈ N := Subgroup.subset_normalClosure (Or.inl ⟨s, hs, rfl⟩)
      exact (QuotientGroup.eq_one_iff (b s)).mpr hs'
    intro x hx
    have ha : a x ∈ g.ker := by
      change (g.comp a) x = 1
      rw [hga]
      exact hx
    apply (QuotientGroup.eq_one_iff x).mp
    change q x = 1
    rw [hq]
    exact hgq ha

private def freeGenerators : Generators (FreeGroup (Fin 7)) :=
  ⟨FreeGroup.of 0, FreeGroup.of 1, FreeGroup.of 2, FreeGroup.of 3, FreeGroup.of 4,
    FreeGroup.of 5, FreeGroup.of 6⟩

private def matrixLift : FreeGroup (Fin 7) →* Triangular :=
  FreeGroup.lift ![matrixGenerators.a, matrixGenerators.b, matrixGenerators.c,
    matrixGenerators.d, matrixGenerators.e, matrixGenerators.t, matrixGenerators.s]

private theorem freeGenerators_map_matrixLift :
    freeGenerators.map matrixLift = matrixGenerators := by
  simp [freeGenerators, matrixLift, Generators.map, matrixGenerators]

private noncomputable def relators : Finset (FreeGroup (Fin 7)) := by
  classical
  exact (freeGenerators.rootWord 0 :: freeGenerators.structuralRelators).toFinset

private instance torsionFreeRelationsNormal {n : ℕ} (S : Set (FreeGroup (Fin n))) :
    (torsionFreeRelations S).Normal where
  conj_mem := by
    intro x hx g
    rw [torsionFreeRelations, Subgroup.mem_sInf] at hx ⊢
    intro N hN
    exact hN.1.conj_mem x (hx N hN) g

private theorem subset_torsionFreeRelations {n : ℕ} (S : Set (FreeGroup (Fin n))) :
    S ⊆ torsionFreeRelations S := by
  intro x hx
  change x ∈ torsionFreeRelations S
  rw [torsionFreeRelations, Subgroup.mem_sInf]
  exact fun _ hN => hN.2.1 hx

private theorem torsionFreeRelations_root {n : ℕ} (S : Set (FreeGroup (Fin n)))
    {x : FreeGroup (Fin n)} {k : ℕ} (hk : 0 < k) (hx : x ^ k ∈ torsionFreeRelations S) :
    x ∈ torsionFreeRelations S := by
  rw [torsionFreeRelations, Subgroup.mem_sInf] at hx ⊢
  exact fun N hN => hN.2.2 x k hk (hx N hN)

private theorem relations_le_shears :
    torsionFreeRelations (relators : Set (FreeGroup (Fin 7))) ≤
      (shearSubgroup ⊤).comap matrixLift := by
  classical
  apply sInf_le
  refine ⟨inferInstance, ?_, ?_⟩
  · intro w hw
    change matrixLift w ∈ shearSubgroup ⊤
    have hw' : w ∈ freeGenerators.rootWord 0 :: freeGenerators.structuralRelators :=
      List.mem_toFinset.mp hw
    rcases List.mem_cons.mp hw' with rfl | hw'
    · rw [Generators.map_rootWord, freeGenerators_map_matrixLift, matrix_rootWord]
      exact ⟨_, trivial, rfl⟩
    · have h : matrixLift w ∈ matrixGenerators.structuralRelators := by
        rw [← freeGenerators_map_matrixLift, ← Generators.map_structuralRelators]
        exact List.mem_map_of_mem hw'
      rw [matrix_structuralRelators _ h]
      exact (shearSubgroup ⊤).one_mem
  · intro w k hk hw
    apply shear_root_closed _ k hk
    rw [← map_pow]
    exact hw

/--
**Budkin's theorem (Kourovka Problem 18.17).** There is a torsion-free group $G$ (no element of $G$
other than the identity has finite order) that is finitely presented in the quasivariety of
torsion-free groups but is not a finitely presented group.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 18.17 (O. V.
Belegradek); resolution: A. I. Budkin, Siberian Electron. Math. Rep. 14 (2017), 937-945, Kourovka
Archive, Problem 18.17: Yes, there is, http://semr.math.nsc.ru.
-/
public theorem torsionFreePresentedNotFinitelyPresented_holds :
    torsionFreePresentedNotFinitelyPresented := by
  classical
  let S : Set (FreeGroup (Fin 7)) := relators
  let R := torsionFreeRelations S
  let q := QuotientGroup.mk' R
  have hpow (g : FreeGroup (Fin 7) ⧸ R) (k : ℕ) (hk : 0 < k) (hg : g ^ k = 1) : g = 1 := by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R g
    apply (QuotientGroup.eq_one_iff x).2
    apply torsionFreeRelations_root S hk
    apply (QuotientGroup.eq_one_iff (x ^ k)).1
    exact (map_pow q x k).trans hg
  refine ⟨_, inferInstance, ?_, ⟨7, relators, q, QuotientGroup.mk'_surjective R,
    QuotientGroup.ker_mk' R⟩, ?_⟩
  · intro g hg h
    obtain ⟨k, hk, hgk⟩ := h.exists_pow_eq_one
    exact hg (hpow g k hk hgk)
  · -- Every word in the square-root sequence is killed by the quotient.
    have hRel (w : FreeGroup (Fin 7)) (hw : w ∈
        freeGenerators.rootWord 0 :: freeGenerators.structuralRelators) : q w = 1 :=
      (QuotientGroup.eq_one_iff w).2 (subset_torsionFreeRelations S (List.mem_toFinset.mpr hw))
    have hSq (k : ℕ) : q (freeGenerators.rootWord (k + 1)) ^ 2 = q (freeGenerators.rootWord k) := by
      simp only [Generators.map_rootWord]
      refine (freeGenerators.map q).rootWord_sq ?_ k
      intro w hw
      rw [← Generators.map_structuralRelators] at hw
      obtain ⟨w', hw', rfl⟩ := List.mem_map.mp hw
      exact hRel w' (List.mem_cons_of_mem _ hw')
    have hRoots (k : ℕ) : freeGenerators.rootWord k ∈ R := by
      apply (QuotientGroup.eq_one_iff _).1
      change q (freeGenerators.rootWord k) = 1
      induction k with
      | zero => exact hRel _ (List.mem_cons_self ..)
      | succ k ih => exact hpow _ 2 (by decide) ((hSq k).trans ih)
    -- Any finite set of normal generators would put a common denominator on all the shears.
    intro hfp
    have hFG := finite_normal_kernel q (QuotientGroup.mk'_surjective R) hfp
    rw [QuotientGroup.ker_mk'] at hFG
    obtain ⟨T, hT, hTR⟩ := hFG
    obtain ⟨D, hD, hDT⟩ := finite_subset_boundedDenominator (hT.image (Triangular.z ∘ matrixLift))
    let N := (shearSubgroup (boundedDenominator D)).comap matrixLift
    have hRN : R ≤ N := by
      rw [← hTR]
      apply Subgroup.normalClosure_le_normal
      intro w hw
      have hR : w ∈ R := hTR ▸ Subgroup.subset_normalClosure hw
      obtain ⟨r, _, hr⟩ := relations_le_shears hR
      have hrz : r = (matrixLift w).z := congrArg Triangular.z hr
      exact ⟨r, hrz ▸ hDT ⟨w, hw, rfl⟩, hr⟩
    have hz : matrixLift (freeGenerators.rootWord D) ∈ shearSubgroup (boundedDenominator D) :=
      hRN (hRoots D)
    rw [Generators.map_rootWord, freeGenerators_map_matrixLift, matrix_rootWord, shear_mem] at hz
    exact inverse_two_pow_not_mem D hD hz

end MathlibExt.GroupTheory.TorsionFreeQuasivarietyPresentationKourovka18Problem17Wanted
