/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/GroupTheory/UnitConjecture.lean` (leanprover/lean-eval, commit
38361be884302c7edce1908c4aef8296eb2cb27e), problem `annals_unit_conjecture`.
Copyright 2026 Lean FRO, LLC.
Author (problem submitter): Thomas Browning.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The definitions and statement of Theorem A come from this problem, which credits
`AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean` (AnnalsChallenge v1.0.0).
lean-eval ships no `NOTICE` file.

Modification notice (Apache License 2.0, Section 4). ATLAS placed the problem in its own
namespace and recorded the statement with Batteries' `theorem_wanted`. This module moves the
definitions and statement from the wanted library and adds the proof.
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.GroupTheory.PresentedGroup
import Mathlib.Algebra.CharP.Two
import Mathlib.Tactic.Group

/-!
# Gardam's counterexample to the unit conjecture

Gardam's Theorem A exhibits a nontrivial unit in the group ring of a torsion-free group
over the field with two elements. We compute in the four cosets of its translation subgroup.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.UnitConjectureWanted

set_option autoImplicit false

noncomputable section

namespace UnitConjecture

/-- **Generators of Gardam's presentation.** This is the two-element set consisting of the
distinct formal symbols $a$ and $b$, which serve as the generators of the group presentation in
Theorem A of Gardam's counterexample to the unit conjecture. -/
inductive generators where
  | a
  | b

/-- **First free generator of Gardam's presentation.** $a$ is the generator $a$, viewed as an
element of the free group on the two generators $a$ and $b$. -/
def a : FreeGroup generators := .of generators.a

/-- **Second free generator of Gardam's presentation.** $b$ is the generator $b$, viewed as an
element of the free group on the two generators $a$ and $b$. -/
def b : FreeGroup generators := .of generators.b

/-- **Relators of Gardam's group.** In the free group on the generators $a$ and $b$, the relators
are the two elements $b^{-1}a^2ba^2$ and $a^{-1}b^2ab^2$.

Imposing them gives the relations $b^{-1}a^2b = a^{-2}$ and $a^{-1}b^2a = b^{-2}$ of Theorem A of
Gardam's counterexample to the unit conjecture. -/
def relations : Set (FreeGroup generators) :=
  {b⁻¹ * a ^ 2 * b * a ^ 2, a⁻¹ * b ^ 2 * a * b ^ 2}

/-- **Gardam's group.** $P$ is the group with generators $a$ and $b$ and relators
$b^{-1}a^2ba^2$ and $a^{-1}b^2ab^2$, that is,
$P = \langle a, b \mid b^{-1}a^2b = a^{-2}, a^{-1}b^2a = b^{-2} \rangle$.

This is the group of Theorem A of Gardam's counterexample to the unit conjecture. -/
def P := PresentedGroup relations
deriving Coe (FreeGroup generators), Group

/-- **The element x of Gardam's group.** In the group $P$ with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, $x = a^2$. -/
def x : P := a ^ 2

/-- **The element y of Gardam's group.** In the group $P$ with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, $y = b^2$. -/
def y : P := b ^ 2

/-- **The element z of Gardam's group.** In the group $P$ with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, $z = (ab)^2$. -/
def z : P := (a * b) ^ 2

/-- **Group ring of Gardam's group over the field with two elements.** $\mathbb{F}_2[P]$ is the
group ring of Gardam's group $P$ over the field $\mathbb{F}_2 = \mathbb{Z}/2\mathbb{Z}$. -/
abbrev R := MonoidAlgebra (ZMod 2) P

instance : Coe P R where
  coe := MonoidAlgebra.of (ZMod 2) P

/-- **Gardam's element p.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $p$ is the element $(1 + x)(1 + y)(1 + z^{-1})$ of $\mathbb{F}_2[P]$. -/
def p : R := (1 + x) * (1 + y) * (1 + z⁻¹)

/-- **Gardam's element q.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $q$ is the element $x^{-1}y^{-1} + x + y^{-1}z + z$ of $\mathbb{F}_2[P]$. -/
def q : R := x⁻¹ * y⁻¹ + x + y⁻¹ * z + z

/-- **Gardam's element r.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $r$ is the element $1 + x + y^{-1}z + xyz$ of $\mathbb{F}_2[P]$. -/
def r : R := 1 + x + y⁻¹ * z + x * y * z

/-- **Gardam's element s.** In the group ring $\mathbb{F}_2[P]$ of Gardam's group $P$ with
generators $a$ and $b$, let $x = a^2$, $y = b^2$ and $z = (ab)^2$ in $P$, viewed as elements of
$\mathbb{F}_2[P]$. Then $s$ is the element $1 + (x + x^{-1} + y + y^{-1})z^{-1}$ of
$\mathbb{F}_2[P]$. -/
def s : R := 1 + (x + x⁻¹ + y + y⁻¹) * z⁻¹

/-- **Gardam's unit.** Let $P$ be the group with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$ and set $x = a^2$,
$y = b^2$, $z = (ab)^2$. In the group ring $\mathbb{F}_2[P]$, $u = p + qa + rb + sab$, where
$p = (1 + x)(1 + y)(1 + z^{-1})$, $q = x^{-1}y^{-1} + x + y^{-1}z + z$,
$r = 1 + x + y^{-1}z + xyz$ and $s = 1 + (x + x^{-1} + y + y^{-1})z^{-1}$. -/
def u : R := p + q * a + r * b + s * (a * b)

local notation "A" => (a : P)
local notation "B" => (b : P)

-- Normal forms are xⁱ yʲ zᵏ times one of four coset representatives.
private inductive Coset | e | a | b | ab
  deriving DecidableEq

private abbrev Lattice := ℤ × ℤ × ℤ

private def action : Coset → Lattice → Lattice
  | .e, v => v
  | .a, (i, j, k) => (i, -j, -k)
  | .b, (i, j, k) => (-i, j, -k)
  | .ab, (i, j, k) => (-i, -j, k)

-- The translation and representative of each product in Gardam's factor table.
private def factor : Coset → Coset → Lattice × Coset
  | .e, t | t, .e => (0, t)
  | .a, .a => ((1, 0, 0), .e)
  | .a, .b => (0, .ab)
  | .a, .ab => ((1, 0, 0), .b)
  | .b, .a => ((-1, 1, -1), .ab)
  | .b, .b => ((0, 1, 0), .e)
  | .b, .ab => ((-1, 0, -1), .a)
  | .ab, .a => ((0, -1, 1), .b)
  | .ab, .b => ((0, -1, 0), .a)
  | .ab, .ab => ((0, 0, 1), .e)

private structure Normal where
  vec : Lattice
  tail : Coset
  deriving DecidableEq

private def multiply (g h : Normal) : Normal :=
  ⟨g.vec + action g.tail h.vec + (factor g.tail h.tail).1, (factor g.tail h.tail).2⟩

private def inverse (g : Normal) : Normal :=
  ⟨-action g.tail g.vec - (factor g.tail g.tail).1, g.tail⟩

private theorem action_add (t : Coset) (v w : Lattice) :
    action t (v + w) = action t v + action t w := by
  cases t <;> simp [action, Prod.add_def, add_comm]

private theorem action_comp (t u : Coset) (v : Lattice) :
    action (factor t u).2 v = action t (action u v) := by
  cases t <;> cases u <;> simp [action, factor]

private theorem cocycle (t u v : Coset) :
    (factor t u).1 + (factor (factor t u).2 v).1 =
      action t (factor u v).1 + (factor t (factor u v).2).1 := by
  cases t <;> cases u <;> cases v <;> decide

private instance normalGroup : Group Normal where
  one := ⟨0, .e⟩
  mul := multiply
  inv := inverse
  one_mul := by
    intro g
    change multiply ⟨0, .e⟩ g = g
    simp [multiply, action, factor]
  mul_one := by
    rintro ⟨v, t⟩
    change multiply _ ⟨0, .e⟩ = _
    cases t <;> simp [multiply, action, factor]
  inv_mul_cancel := by
    rintro ⟨⟨i, j, k⟩, t⟩
    change multiply (inverse _) _ = ⟨0, .e⟩
    cases t <;> simp [multiply, inverse, action, factor, Prod.add_def, Prod.sub_def] <;> omega
  mul_assoc := by
    rintro ⟨l, t⟩ ⟨m, u⟩ ⟨n, v⟩
    change multiply (multiply _ _) _ = multiply _ (multiply _ _)
    simp only [multiply, Normal.mk.injEq, action_add, action_comp]
    constructor
    · calc
        _ = (l + action t m + action t (action u n)) +
            ((factor t u).1 + (factor (factor t u).2 v).1) := by ac_rfl
        _ = _ := by rw [cocycle]; ac_rfl
    · cases t <;> cases u <;> cases v <;> rfl

private def generator : generators → Normal
  | .a => ⟨0, .a⟩
  | .b => ⟨0, .b⟩

private def coordinates : P →* Normal :=
  PresentedGroup.toGroup (f := generator) (by
    rintro w (rfl | h)
    · simp only [map_mul, map_inv, map_pow, a, b, FreeGroup.lift_apply_of]
      decide
    · obtain rfl : w = _ := h
      simp only [map_mul, map_inv, map_pow, a, b, FreeGroup.lift_apply_of]
      decide)

private theorem coordinates_a : coordinates A = generator .a :=
  PresentedGroup.toGroup.of _

private theorem coordinates_b : coordinates B = generator .b :=
  PresentedGroup.toGroup.of _

private theorem reverses_of_relator {g h : P} (rel : g⁻¹ * h * g * h = 1) :
    SemiconjBy g h h⁻¹ := by
  have he : g⁻¹ * h * g = h⁻¹ := eq_inv_of_mul_eq_one_left rel
  have hs : SemiconjBy g h⁻¹ h := by
    rw [SemiconjBy, ← he]
    group
  simpa using hs.inv_right

private theorem a_y : SemiconjBy A y y⁻¹ :=
  reverses_of_relator (PresentedGroup.one_of_mem (rels := relations)
    (x := a⁻¹ * b ^ 2 * a * b ^ 2) (by simp [relations]))

private theorem b_x : SemiconjBy B x x⁻¹ :=
  reverses_of_relator (PresentedGroup.one_of_mem (rels := relations)
    (x := b⁻¹ * a ^ 2 * b * a ^ 2) (by simp [relations]))

private theorem ba_sq : (B * A) ^ 2 = z⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  calc
    (B * A) ^ 2 * z = B * A * B * (x * B) * A * B := by simp [x, z, sq, mul_assoc]
    _ = B * A * B * (B * x⁻¹) * A * B := by rw [b_x.inv_right.eq]; simp
    _ = B * (A * y) * A⁻¹ * B := by unfold x y; simp only [sq]; group
    _ = B * (y⁻¹ * A) * A⁻¹ * B := by rw [a_y.eq]
    _ = 1 := by unfold y; group

private theorem a_z : SemiconjBy A z z⁻¹ := by
  have h : SemiconjBy A z⁻¹ z := by rw [SemiconjBy, ← ba_sq]; simp [z, sq, mul_assoc]
  simpa using h.inv_right

private theorem b_z : SemiconjBy B z z⁻¹ := by
  rw [SemiconjBy, ← ba_sq]
  simp [z, sq, mul_assoc]

private theorem square_commutes {g h : P} (hs : SemiconjBy g h h⁻¹) : Commute (g ^ 2) h := by
  simpa [sq, Commute] using hs.inv_right.mul_left hs

private theorem xy : Commute x y := square_commutes a_y
private theorem xz : Commute x z := square_commutes a_z
private theorem yz : Commute y z := square_commutes b_z

private def translation (v : Lattice) : P := x ^ v.1 * y ^ v.2.1 * z ^ v.2.2

private theorem translation_add (v w : Lattice) :
    translation (v + w) = translation v * translation w := by
  obtain ⟨i, j, k⟩ := v
  obtain ⟨l, m, n⟩ := w
  simp only [translation, Prod.fst_add, Prod.snd_add, zpow_add]
  rw [(xy.zpow_zpow l j).mul_mul_mul_comm]
  simp only [mul_assoc, ((xz.zpow_zpow l k).symm).left_comm,
    ((yz.zpow_zpow m k).symm).left_comm]

private def representative : Coset → P
  | .e => 1
  | .a => A
  | .b => B
  | .ab => A * B

private theorem representative_action (t : Coset) (v : Lattice) :
    SemiconjBy (representative t) (translation v) (translation (action t v)) := by
  obtain ⟨i, j, k⟩ := v
  have actA (i j k : ℤ) :
      SemiconjBy A (translation (i, j, k)) (translation (action .a (i, j, k))) := by
    simpa [translation, action, x, y, inv_zpow, zpow_neg] using
      (((Commute.self_pow A 2).semiconjBy.zpow_right i).mul_right
        (a_y.zpow_right j)).mul_right (a_z.zpow_right k)
  have actB (i j k : ℤ) :
      SemiconjBy B (translation (i, j, k)) (translation (action .b (i, j, k))) := by
    simpa [translation, action, x, y, inv_zpow, zpow_neg] using
      ((b_x.zpow_right i).mul_right
        ((Commute.self_pow B 2).semiconjBy.zpow_right j)).mul_right (b_z.zpow_right k)
  cases t with
  | e => exact SemiconjBy.one_left _
  | a => exact actA i j k
  | b => exact actB i j k
  | ab => simpa [action, representative] using (actA (-i) j (-k)).mul_left (actB i j k)

private theorem ba_eq : B * A = x⁻¹ * y * z⁻¹ * (A * B) := by
  have swap : x⁻¹ * B⁻¹ = B⁻¹ * x := by
    simpa using congrArg Inv.inv b_x.eq
  rw [xy.inv_left.eq]
  calc
    B * A = y * B⁻¹ * x * A⁻¹ := by unfold x y; group
    _ = y * (x⁻¹ * B⁻¹) * A⁻¹ := by rw [swap, mul_assoc y]
    _ = y * x⁻¹ * z⁻¹ * (A * B) := by unfold z; simp only [sq]; group

private theorem representative_mul (t u : Coset) :
    representative t * representative u =
      translation (factor t u).1 * representative (factor t u).2 := by
  have habb : A * B * B = y⁻¹ * A := by simpa [y, sq, mul_assoc] using a_y.eq
  have haba : A * B * A = y⁻¹ * z * B := by
    rw [yz.inv_left.eq]
    unfold y z
    simp only [sq]
    group
  have hbab : B * (A * B) = x⁻¹ * z⁻¹ * A := by
    rw [← mul_assoc, ba_eq, mul_assoc _ (A * B), habb]
    simp only [mul_assoc, yz.inv_right.inv_left.symm.left_comm, mul_inv_cancel_left]
  cases t <;> cases u <;>
    simp only [representative, factor, translation, Prod.fst_zero, Prod.snd_zero, zpow_zero,
      zpow_one, zpow_neg_one, one_mul, mul_one] <;>
    first | exact ba_eq | exact habb | exact haba | exact hbab | simp [x, y, z, sq, mul_assoc]

private def decode : Normal →* P where
  toFun g := translation g.vec * representative g.tail
  map_one' := by change translation (0 : Lattice) * 1 = 1; simp [translation]
  map_mul' g h := by
    change translation (_ + _ + _) * representative (factor _ _).2 = _
    rw [translation_add, translation_add, mul_assoc _ (translation (factor _ _).1),
      ← representative_mul]
    simp only [mul_assoc]
    rw [← mul_assoc (translation (action _ _)), ← (representative_action g.tail h.vec).eq,
      mul_assoc]

private theorem decode_comp_coordinates : decode.comp coordinates = MonoidHom.id P := by
  apply PresentedGroup.ext
  rintro (_ | _)
  · change decode (coordinates A) = A
    rw [coordinates_a]
    change translation 0 * A = A
    simp [translation]
  · change decode (coordinates B) = B
    rw [coordinates_b]
    change translation 0 * B = B
    simp [translation]

-- A square is always a translation. On each nonidentity coset one component
-- of its translation vector is odd.
private theorem torsion_free (g : Normal) (n : ℕ) (hn : n ≠ 0) (hg : g ^ n = 1) : g = 1 := by
  have pure_pow (v : Lattice) (j : ℕ) :
      (⟨v, .e⟩ : Normal) ^ j = ⟨j • v, .e⟩ := by
    induction j with
    | zero => simp only [pow_zero, zero_smul]; rfl
    | succ j ih =>
      rw [pow_succ, ih, succ_nsmul]
      change multiply _ _ = _
      simp [multiply, action, factor]
  have hs : (g * g) ^ n = 1 := by rw [← sq, ← pow_mul, Nat.mul_comm, pow_mul, hg, one_pow]
  have pure : g * g = ⟨(g * g).vec, .e⟩ := by
    obtain ⟨v, t⟩ := g
    cases t <;> rfl
  rw [pure, pure_pow] at hs
  have hv : n • (g * g).vec = 0 := congrArg Normal.vec hs
  have h := (nsmul_eq_zero_iff_right hn).mp hv
  obtain ⟨⟨i, j, k⟩, t⟩ := g
  change (multiply _ _).vec = 0 at h
  change Normal.mk _ _ = ⟨0, .e⟩
  cases t <;> simp [multiply, factor, action, Prod.add_def, Prod.ext_iff] at h ⊢ <;> omega

-- Interpret lists of group elements as sums of basis vectors over the field of two elements.
private abbrev CoordinateRing := MonoidAlgebra (ZMod 2) Normal

private abbrev basis := MonoidAlgebra.of (ZMod 2) Normal

private def evaluate (l : List Normal) : CoordinateRing := (l.map basis).sum

private def convolve (l m : List Normal) : List Normal := l.flatMap fun g => m.map (g * ·)

private theorem evaluate_append (l m : List Normal) :
    evaluate (l ++ m) = evaluate l + evaluate m := by simp [evaluate]

private theorem evaluate_convolve (l m : List Normal) :
    evaluate (convolve l m) = evaluate l * evaluate m := by
  induction l with
  | nil => simp [convolve, evaluate]
  | cons g l ih =>
    rw [convolve, List.flatMap_cons, evaluate_append]
    change _ + evaluate (convolve l m) = _
    rw [ih]
    simp only [evaluate, List.map_map, Function.comp_def, map_mul, List.sum_map_mul_left,
      List.map_cons, List.sum_cons, add_mul]

private def cancelPairs : List Normal → List Normal
  | [] => []
  | g :: l =>
    let rest := cancelPairs l
    if g ∈ rest then rest.erase g else g :: rest

private theorem evaluate_cancelPairs (l : List Normal) : evaluate (cancelPairs l) = evaluate l := by
  induction l with
  | nil => rfl
  | cons g l ih =>
    change _ = basis g + evaluate l
    rw [← ih, cancelPairs]
    split_ifs with h
    · have he := ((List.perm_cons_erase h).map basis).sum_eq
      change evaluate (cancelPairs l) = basis g + evaluate _ at he
      rw [he, ← add_assoc]
      have hg : basis g + basis g = 0 := by
        rw [MonoidAlgebra.of_apply, ← MonoidAlgebra.single_add, CharTwo.add_self_eq_zero,
          MonoidAlgebra.single_zero]
      rw [hg, zero_add]
    · rfl

local notation "α" => generator generators.a
local notation "β" => generator generators.b
local notation "X" => (α ^ 2)
local notation "Y" => (β ^ 2)
local notation "Z" => ((α * β) ^ 2)
local infixl:70 " ⋆ " => convolve

private def pTerms := [1, X] ⋆ [1, Y] ⋆ [1, Z⁻¹]
private def qTerms := [X⁻¹ * Y⁻¹, X, Y⁻¹ * Z, Z]
private def rTerms := [1, X, Y⁻¹ * Z, X * Y * Z]
private def sTerms := [1] ++ [X, X⁻¹, Y, Y⁻¹] ⋆ [Z⁻¹]

private def unitTerms :=
  pTerms ++ qTerms ⋆ [α] ++ rTerms ⋆ [β] ++ sTerms ⋆ [α * β]

-- In characteristic two the coefficients of Gardam's inverse are
-- x⁻¹ pᵃ, x⁻¹ q, y⁻¹ r, z⁻¹ sᵃ, where conjugation by a inverts y and z.
private def inverseTerms :=
  [1, X⁻¹] ⋆ [1, Y⁻¹] ⋆ [1, Z] ++ [X⁻¹] ⋆ qTerms ⋆ [α] ++
    [Y⁻¹] ⋆ rTerms ⋆ [β] ++ [Z⁻¹, X, X⁻¹, Y, Y⁻¹] ⋆ [α * β]

private def encodeRing := MonoidAlgebra.mapDomainRingHom (ZMod 2) coordinates

private theorem encode_basis (g : P) :
    encodeRing (MonoidAlgebra.of (ZMod 2) P g) = basis (coordinates g) :=
  MonoidAlgebra.mapDomain_single ..

private theorem encode_unit : encodeRing u = evaluate unitTerms := by
  simp only [u, p, q, r, s, x, y, z, map_add, map_mul, map_one, encode_basis, map_pow,
    map_inv, coordinates_a, coordinates_b, unitTerms, pTerms, qTerms, rTerms, sTerms,
    evaluate_append, evaluate_convolve]
  simp only [evaluate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
    map_one, map_mul, map_pow, add_assoc]

set_option maxRecDepth 4096 in
private theorem unit_in_coordinates : IsUnit (evaluate unitTerms) := by
  have product (l m : List Normal) (h : cancelPairs (l ⋆ m) = [1]) :
      evaluate l * evaluate m = 1 := by
    rw [← evaluate_convolve, ← evaluate_cancelPairs, h]
    simp only [evaluate, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero,
      map_one]
  have right := product unitTerms inverseTerms (by decide +kernel)
  have left := product inverseTerms unitTerms (by decide +kernel)
  exact ⟨⟨_, _, right, left⟩, rfl⟩

private theorem evaluate_coeff (l : List Normal) (g : Normal) :
    (evaluate l).coeff g = (l.count g : ZMod 2) := by
  induction l with
  | nil => simp [evaluate]
  | cons h l ih =>
    change (basis h + evaluate l).coeff g = _
    by_cases he : h = g <;>
      simp [MonoidAlgebra.coeff_add, he, ih, add_comm]

private theorem not_basis (g : Normal) : evaluate unitTerms ≠ basis g := by
  intro h
  have hit (v : Normal) (hv : unitTerms.count v = 1) : g = v := by
    by_contra hn
    have he := congrArg (fun f : CoordinateRing => f.coeff v) h
    simp [evaluate_coeff, hv, hn] at he
  have h₁ := hit 1 (by decide)
  have h₂ := hit X (by decide)
  exact (by decide : (1 : Normal) ≠ X) (h₁.symm.trans h₂)

/--
**Gardam's counterexample to the unit conjecture.** Let $P$ be the group with presentation
$\langle a, b \mid b^{-1}a^2b = a^{-2},\ a^{-1}b^2a = b^{-2} \rangle$, and set $x = a^2$,
$y = b^2$ and $z = (ab)^2$. In the group ring $\mathbb{F}_2[P]$ set
$p = (1 + x)(1 + y)(1 + z^{-1})$, $q = x^{-1}y^{-1} + x + y^{-1}z + z$,
$r = 1 + x + y^{-1}z + xyz$ and $s = 1 + (x + x^{-1} + y + y^{-1})z^{-1}$, and let
$u = p + qa + rb + sab$. Then $P$ is torsion-free (if $g \in P$ and $g^n = 1$ for some
natural number $n \neq 0$, then $g = 1$), $u$ is a unit of $\mathbb{F}_2[P]$, and $u$ is not
equal to any element $g$ of $P$ viewed in $\mathbb{F}_2[P]$; that is, $u$ is a non-trivial unit.

Source: G. Gardam, `A counterexample to the unit conjecture for group rings`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-UnitConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_unit_conjecture`.
-/
public theorem theorem_A :
    (∀ g : P, ∀ n ≠ 0, g ^ n = 1 → g = 1) ∧ IsUnit u ∧ ¬ ∃ g : P, u = g := by
  refine ⟨?_, ?_, ?_⟩
  · intro g n hn hg
    have h := torsion_free (coordinates g) n hn (by rw [← map_pow, hg, map_one])
    calc
      g = decode (coordinates g) := (DFunLike.congr_fun decode_comp_coordinates g).symm
      _ = 1 := by rw [h, map_one]
  · have hu := unit_in_coordinates.map (MonoidAlgebra.mapDomainRingHom (ZMod 2) decode)
    rw [← encode_unit] at hu
    change IsUnit ((MonoidAlgebra.mapDomainRingHom (ZMod 2) decode |>.comp encodeRing) u) at hu
    simpa only [encodeRing, ← MonoidAlgebra.mapDomainRingHom_comp, decode_comp_coordinates,
      MonoidAlgebra.mapDomainRingHom_id, RingHom.id_apply] using hu
  · rintro ⟨g, hg⟩
    apply not_basis (coordinates g)
    rw [← encode_unit, hg]
    exact encode_basis g

end UnitConjecture
end
end MathlibExt.GroupTheory.UnitConjectureWanted
