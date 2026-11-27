/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Solvable
public import MathlibExt.GroupTheory.WordProblemSolvableShared
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Computability.Halting
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Reduce
import Mathlib.Data.Finsupp.Lex
import Mathlib.Order.Prod.Lex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import MathlibExt.Computability.RE

/-!
# Soluble right-orderable groups with insoluble word problem (Kourovka Notebook Problem 17.28)

Kourovka Notebook, Archive of Solved Problems, Problem 17.28 (V. V. Bludov, A. M. W. Glass): is
there a soluble right-orderable group with insoluble word problem?

We prove the existence statement with three generators. A shift and two unipotent elements
generate a soluble right-ordered group over the integer Laurent polynomials. A commutator word
for each natural number has a single central coefficient, which vanishes exactly when the
corresponding program halts on zero.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 17.28 (V. V.
Bludov, A. M. W. Glass). UnsolvedMath record UM-00701330 (`KOU-17.28`), dataset ulamai/UnsolvedMath
v1.8.0.

The word problem is posed, as in the resolution, for finitely generated recursively presented
groups: for a finite generating family `gens : Fin k → G` it is the set of words (lists of letters
`(i, ε)`, `ε = false` for an inverse) that spell `1`. The group is recursively presented when this
set is recursively enumerable (`REPred`; for a finitely generated group this is the same as having a
presentation with a recursively enumerable set of relators), and the word problem is insoluble when
the set is not computable: the shared predicate `WordProblemSolvable (FreeGroup.lift gens)` of
`MathlibExt.GroupTheory.WordProblemSolvableShared` (`ComputablePred` on Mathlib's `Primcodable`
coding of lists) fails. Neither property depends on the finite generating set. Soluble is
`Group.IsSolvable`; right orders are linear orders (as relations) invariant under right
multiplication.
-/

namespace MathlibExt.GroupTheory.SolubleRightOrderableWordProblemKourovka17Problem28Wanted

open MathlibExt.GroupTheory.WordProblemSolvableShared

@[expose] public section

/-- **Recursively presented group.** Let $G$ be a group, $k$ a natural number and $\varphi$ a
homomorphism from the free group on $k$ generators to $G$. The group $G$ is recursively presented
with respect to $\varphi$ when the set of words $w$ (finite lists of letters $(i, \varepsilon)$
with $i < k$ and $\varepsilon$ true or false, the letter $(i, \mathrm{false})$ standing for the
inverse of the $i$-th generator) with $\varphi(w) = 1$ in $G$ is recursively enumerable.

When $\varphi$ is surjective, this is the same as a presentation of $G$ on the images of the
generators with a recursively enumerable set of relators; it is the enumerable counterpart of a
solvable word problem. -/
def IsRecursivelyPresented {G : Type*} [Group G] {k : ℕ} (φ : FreeGroup (Fin k) →* G) : Prop :=
  REPred (fun w : List (Fin k × Bool) => φ (FreeGroup.mk w) = 1)

/-- The right orders of `G`: linear orders (as relations) invariant under right multiplication. -/
def rightOrders (G : Type*) [Group G] : Set (G → G → Prop) :=
  {r | IsLinearOrder G r ∧ ∀ a b c : G, r a b → r (a * c) (b * c)}

/-- **The Bludov–Glass question (Kourovka 17.28).** The statement that there exist a soluble group
$G$ that admits a right order, a natural number $k$ and elements $g_0, \dots, g_{k-1}$ generating
$G$ such that, for the homomorphism $\varphi$ from the free group on $k$ generators to $G$ sending
the $i$-th generator to $g_i$, the group $G$ is recursively presented with respect to $\varphi$
and the word problem for $\varphi$ is not solvable. In words: there is a finitely generated,
recursively presented, soluble right-orderable group with insoluble word problem. -/
def solubleRightOrderableInsolubleWordProblem : Prop :=
  ∃ (G : Type) (_ : Group G), Group.IsSolvable G ∧ (rightOrders G).Nonempty ∧
    ∃ (k : ℕ) (gens : Fin k → G), Subgroup.closure (Set.range gens) = ⊤ ∧
      IsRecursivelyPresented (FreeGroup.lift gens) ∧ ¬ WordProblemSolvable (FreeGroup.lift gens)

end

noncomputable section

open LaurentPolynomial

private abbrev R := LaurentPolynomial ℤ

-- These are coordinates for a nilpotent group of class at most two extended by an integer shift.
-- The shift acts with opposite weights on x and y, so it fixes their product.
-- P projects the central cross term to the coefficients retained in z.
private structure Triangular (P : R →+ R) where
  t : ℤ
  x : R
  y : R
  z : R

variable {P : R →+ R}

private theorem tri_ext {a b : Triangular P} (ht : a.t = b.t) (hx : a.x = b.x)
    (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
  cases a
  cases b
  congr

private def twist (i : ℤ) (f : R) := T i * f

@[local simp] private lemma twist_zero (f : R) : twist 0 f = f := by simp [twist]
@[local simp] private lemma twist_zero_right (i : ℤ) : twist i 0 = 0 := by simp [twist]
@[local simp] private lemma twist_neg (i : ℤ) (f : R) : twist i (-f) = -twist i f := by
  simp [twist]
@[local simp] private lemma twist_add (i : ℤ) (f g : R) :
    twist i (f + g) = twist i f + twist i g := by simp [twist, mul_add]
@[local simp] private lemma twist_twist (i j : ℤ) (f : R) :
    twist i (twist j f) = twist (i + j) f := by simp only [twist, T_add, mul_assoc]
private lemma twist_pair (i j : ℤ) (f g : R) :
    twist (-i) f * twist (i + j) g = f * twist j g := by
  have h : (T (-i) : R) * T (i + j) = T j := by rw [← T_add]; congr 1; abel
  simp only [twist]
  linear_combination f * g * h

private instance triMul : Mul (Triangular P) where
  mul a b := ⟨a.t + b.t, a.x + twist (-a.t) b.x, a.y + twist a.t b.y,
    a.z + b.z + P (a.x * twist a.t b.y)⟩

private instance triOne : One (Triangular P) := ⟨⟨0, 0, 0, 0⟩⟩

private instance triInv : Inv (Triangular P) where
  inv a := ⟨-a.t, -twist a.t a.x, -twist (-a.t) a.y, -a.z + P (a.x * a.y)⟩

@[local simp] private lemma mul_t (a b : Triangular P) : (a * b).t = a.t + b.t := rfl
@[local simp] private lemma mul_x (a b : Triangular P) :
    (a * b).x = a.x + twist (-a.t) b.x := rfl
@[local simp] private lemma mul_y (a b : Triangular P) :
    (a * b).y = a.y + twist a.t b.y := rfl
@[local simp] private lemma mul_z (a b : Triangular P) :
    (a * b).z = a.z + b.z + P (a.x * twist a.t b.y) := rfl
@[local simp] private lemma one_t : (1 : Triangular P).t = 0 := rfl
@[local simp] private lemma one_x : (1 : Triangular P).x = 0 := rfl
@[local simp] private lemma one_y : (1 : Triangular P).y = 0 := rfl
@[local simp] private lemma one_z : (1 : Triangular P).z = 0 := rfl

private instance triGroup : Group (Triangular P) where
  mul_assoc a b c := by
    apply tri_ext
    · exact add_assoc ..
    · simp [add_assoc, add_comm (-b.t) (-a.t)]
    · simp [add_assoc]
    · simp only [mul_z, mul_x, mul_t, mul_y, twist_add, twist_twist, add_mul, mul_add, map_add,
        twist_pair]
      abel
  one_mul a := by apply tri_ext <;> simp
  mul_one a := by apply tri_ext <;> simp
  inv_mul_cancel a := by
    apply tri_ext
    · exact neg_add_cancel _
    · change -_ + twist (- -a.t) _ = 0
      simp
    · exact neg_add_cancel _
    · change (-a.z + P (a.x * a.y)) + a.z + P (-twist a.t a.x * twist (-a.t) a.y) = 0
      have h := twist_pair (-a.t) 0 a.x a.y
      simp only [neg_neg, add_zero, twist_zero] at h
      simp [h, add_comm]

-- The shift quotient, the pair of off-diagonal entries in its kernel, and the center
-- give three successive abelian factors.
private def shiftHom : Triangular P →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd a.t
  map_one' := rfl
  map_mul' _ _ := rfl

private lemma ker_t (a : (shiftHom (P := P)).ker) : a.val.t = 0 := a.property

private def baseHom : (shiftHom (P := P)).ker →* Multiplicative (R × R) where
  toFun a := Multiplicative.ofAdd (a.val.x, a.val.y)
  map_one' := rfl
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    change ((a.val * b.val).x, (a.val * b.val).y) = (_, _)
    simp [ker_t]

private theorem tri_solvable : Group.IsSolvable (Triangular P) := by
  have : Group.IsSolvable (baseHom (P := P)).ker := by
    apply Group.isSolvable_of_comm
    intro a b
    have h (c : (baseHom (P := P)).ker) : (c.val.val.x, c.val.val.y) = (0, 0) := c.property
    apply Subtype.ext
    apply Subtype.ext
    apply tri_ext (a := a.val.val * b.val.val) (b := b.val.val * a.val.val)
    all_goals simp [ker_t, (Prod.mk.inj (h a)).1, (Prod.mk.inj (h b)).1, add_comm]
  have : Group.IsSolvable (shiftHom (P := P)).ker :=
    Group.isSolvable_of_ker_le_range baseHom.ker.subtype baseHom (by simp)
  exact Group.isSolvable_of_ker_le_range shiftHom.ker.subtype shiftHom (by simp)

-- With t fixed, right multiplication translates x and y. With x fixed as well,
-- it also translates z. Thus the lexicographic order on these coordinates works.
private abbrev CoeffOrder := Lex (ℤ →₀ ℤ)
private def ordR (f : R) : CoeffOrder := toLex f.coeff
private def coord (a : Triangular P) : ℤ ×ₗ CoeffOrder ×ₗ CoeffOrder ×ₗ CoeffOrder :=
  toLex (a.t, toLex (ordR a.x, toLex (ordR a.y, ordR a.z)))

private theorem ordR_inj : Function.Injective ordR := AddMonoidAlgebra.coeff_injective

private theorem coord_inj : Function.Injective (coord (P := P)) := by
  intro a b h
  change (a.t, ordR a.x, ordR a.y, ordR a.z) = (b.t, ordR b.x, ordR b.y, ordR b.z) at h
  simp only [Prod.mk.injEq] at h
  exact tri_ext h.1 (ordR_inj h.2.1) (ordR_inj h.2.2.1) (ordR_inj h.2.2.2)

private lemma ordR_add {a b : R} (h : ordR a < ordR b) (c : R) :
    ordR (a + c) < ordR (b + c) := add_lt_add_left h (ordR c)

private theorem coord_mono (a b c : Triangular P) (h : coord a ≤ coord b) :
    coord (a * c) ≤ coord (b * c) := by
  rcases h.lt_or_eq with h | h
  · apply le_of_lt
    simp only [coord, Prod.Lex.toLex_lt_toLex, mul_t, mul_x, mul_y, mul_z] at h ⊢
    rcases h with ht | ⟨ht, hx | ⟨hx, hy | ⟨hy, hz⟩⟩⟩
    · exact Or.inl (by omega)
    · exact Or.inr ⟨by rw [ht], Or.inl (ht ▸ ordR_add hx _)⟩
    · have ex := ordR_inj hx
      rw [ht, ex]
      exact Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inl (ordR_add hy _)⟩⟩
    · have ex := ordR_inj hx
      have ey := ordR_inj hy
      rw [ht, ex, ey]
      exact Or.inr ⟨rfl, Or.inr ⟨rfl, Or.inr ⟨rfl, ordR_add (ordR_add hz _) _⟩⟩⟩
  · rw [coord_inj h]

-- Words use the shift and the two elementary unipotent matrices, in that order.
private def basis (i : Fin 3) : Triangular P :=
  if i = 0 then ⟨1, 0, 0, 0⟩ else if i = 1 then ⟨0, 1, 0, 0⟩ else ⟨0, 0, 1, 0⟩

-- Encode an integer exponent as a difference of naturals and a Laurent polynomial
-- as a list of signed monomials. Repeated or canceling terms are allowed.
private abbrev Exponent := ℕ × ℕ
private abbrev Term := Exponent × Bool
private abbrev Poly := List Term
private abbrev State := Exponent × Poly × Poly × Poly
private abbrev Letter := Fin 3 × Bool
private abbrev Word := List Letter

private def expVal (a : Exponent) : ℤ := (a.1 : ℤ) - a.2
private def eadd (a b : Exponent) : Exponent := (a.1 + b.1, a.2 + b.2)
private def eneg (a : Exponent) : Exponent := (a.2, a.1)
private def tick (b : Bool) : Exponent := cond b (1, 0) (0, 1)
private def mon (m : Term) : R := cond m.2 (T (expVal m.1)) (-T (expVal m.1))
private def poly (l : Poly) : R := (l.map mon).sum
private def translate (i : Exponent) (b : Bool) (l : Poly) : Poly :=
  l.map fun m => (eadd i m.1, b == m.2)
private def readState (s : State) : Triangular P :=
  ⟨expVal s.1, poly s.2.1, poly s.2.2.1, P (poly s.2.2.2)⟩
private def start : State := ((0, 0), [], [], [])

-- Multiplication on the right by a signed generator uses only shifts and list operations.
private def step (s : State) (c : Letter) : State :=
  if c.1 = 0 then (eadd s.1 (tick c.2), s.2)
  else if c.1 = 1 then (s.1, (eneg s.1, c.2) :: s.2.1, s.2.2)
  else (s.1, s.2.1, (s.1, c.2) :: s.2.2.1, translate s.1 c.2 s.2.1 ++ s.2.2.2)

@[local simp] private lemma exp_add (a b : Exponent) : expVal (eadd a b) = expVal a + expVal b := by
  simp [expVal, eadd]; abel
@[local simp] private lemma exp_neg (a : Exponent) : expVal (eneg a) = -expVal a := by
  simp [expVal, eneg]
@[local simp] private lemma poly_nil : poly [] = 0 := rfl
@[local simp] private lemma poly_cons (m : Term) (l : Poly) : poly (m :: l) = mon m + poly l := rfl
@[local simp] private lemma poly_append (l k : Poly) : poly (l ++ k) = poly l + poly k := by
  simp [poly]

private lemma poly_translate (i : Exponent) (b : Bool) (l : Poly) :
    poly (translate i b l) = cond b (twist (expVal i) (poly l)) (-twist (expVal i) (poly l)) := by
  induction l with
  | nil => cases b <;> simp [translate]
  | cons m l ih =>
    obtain ⟨j, d⟩ := m
    change mon (_, _) + poly (translate i b l) = _
    rw [ih, poly_cons]
    cases b <;> cases d <;> simp [mon, twist, mul_add, -T_mul, ← T_add, add_comm]

private lemma read_start : readState start = (1 : Triangular P) := by
  apply tri_ext <;> simp [readState, start, expVal]

private lemma step_correct (s : State) (c : Letter) :
    readState (P := P) (step s c) = readState s * cond c.2 (basis c.1) (basis c.1)⁻¹ := by
  obtain ⟨i, b⟩ := c
  fin_cases i <;> cases b <;> apply tri_ext <;>
    simp [step, basis, readState, poly_translate, mon, twist, tick, expVal, eadd, eneg,
      Inv.inv, add_assoc, add_comm, add_left_comm, sub_eq_add_neg]

private lemma fold_correct (s : State) (w : Word) :
    readState (P := P) (w.foldl step s) =
      readState s * FreeGroup.lift basis (FreeGroup.mk w) := by
  induction w generalizing s with
  | nil => simp [FreeGroup.lift_mk]
  | cons c w ih => simp [ih, step_correct, FreeGroup.lift_mk, mul_assoc]

private lemma eval_correct (w : Word) :
    readState (P := P) (w.foldl step start) = FreeGroup.lift basis (FreeGroup.mk w) := by
  rw [fold_correct, read_start, one_mul]

-- A coefficient is the difference of the positive and negative counts at its exponent.
private def countTerms (i : Exponent) (b : Bool) (l : Poly) : ℕ :=
  l.foldr (fun m n =>
    if i.1 + m.1.2 = m.1.1 + i.2 ∧ b = m.2 then n + 1 else n) 0

private lemma coeff_poly (l : Poly) (i : Exponent) :
    (poly l).coeff (expVal i) = (countTerms i true l : ℤ) - countTerms i false l := by
  induction l with
  | nil => simp [countTerms]
  | cons m l ih =>
    obtain ⟨j, b⟩ := m
    have he : expVal j = expVal i ↔ i.1 + j.2 = j.1 + i.2 := by unfold expVal; omega
    change _ = (if _ then countTerms i true l + 1 else countTerms i true l : ℕ) -
      ((if _ then countTerms i false l + 1 else countTerms i false l : ℕ) : ℤ)
    cases b <;> by_cases h : i.1 + j.2 = j.1 + i.2 <;> simp [mon, ih, he, h] <;> omega

private lemma coeff_off (l : Poly) (i : ℤ) (h : ∀ m ∈ l, expVal m.1 ≠ i) :
    (poly l).coeff i = 0 := by
  induction l with
  | nil => simp
  | cons m l ih =>
    have hm := h m List.mem_cons_self
    have hl := ih fun d hd => h d (List.mem_cons_of_mem _ hd)
    cases hb : m.2 <;> simp [hl, mon, hb, hm]

-- Discard central coefficients whose exponent, converted to a natural number, belongs to K.
private def mask (K : ℕ → Prop) : R →+ R := by
  classical
  let f : (ℤ →₀ ℤ) →+ (ℤ →₀ ℤ) := Finsupp.filterAddHom (fun i : ℤ => ¬K i.toNat)
  exact AddMonoidAlgebra.coeffAddEquiv.symm.toAddMonoidHom.comp
    (f.comp AddMonoidAlgebra.coeffAddEquiv.toAddMonoidHom)

private lemma mask_eq_zero (K : ℕ → Prop) (f : R) :
    mask K f = 0 ↔ ∀ i : ℤ, K i.toNat ∨ f.coeff i = 0 := by
  classical
  constructor
  · intro h i
    by_cases hi : K i.toNat
    · exact Or.inl hi
    · right
      have he := congrArg (fun a : R => a.coeff i) h
      change (if ¬K i.toNat then f.coeff i else 0) = 0 at he
      simpa [hi] using he
  · intro h
    apply LaurentPolynomial.ext
    intro i
    change (if ¬K i.toNat then f.coeff i else 0) = 0
    rcases h i with hi | hi <;> simp [hi]

private lemma finite_coeff (K : ℕ → Prop) (l : Poly) :
    (∀ i : ℤ, K i.toNat ∨ (poly l).coeff i = 0) ↔
      ∀ m ∈ l, K (m.1.1 - m.1.2) ∨ countTerms m.1 true l = countTerms m.1 false l := by
  have hnat (j : Exponent) : (expVal j).toNat = j.1 - j.2 := by unfold expVal; omega
  constructor
  · intro h m _
    simpa [hnat, coeff_poly, sub_eq_zero] using h (expVal m.1)
  · intro h i
    by_cases hi : ∃ m ∈ l, expVal m.1 = i
    · obtain ⟨m, hm, rfl⟩ := hi
      simpa [hnat, coeff_poly, sub_eq_zero] using h m hm
    · exact Or.inr (coeff_off l i fun m hm he => hi ⟨m, hm, he⟩)

private lemma eval_one (K : ℕ → Prop) (s : State) :
    readState (P := mask K) s = 1 ↔
      s.1.1 = s.1.2 ∧
      (∀ m ∈ s.2.1, countTerms m.1 true s.2.1 = countTerms m.1 false s.2.1) ∧
      (∀ m ∈ s.2.2.1, countTerms m.1 true s.2.2.1 = countTerms m.1 false s.2.2.1) ∧
      ∀ m ∈ s.2.2.2, K (m.1.1 - m.1.2) ∨
        countTerms m.1 true s.2.2.2 = countTerms m.1 false s.2.2.2 := by
  have plain (l : Poly) :
      poly l = 0 ↔ ∀ m ∈ l, countTerms m.1 true l = countTerms m.1 false l := by
    have he : poly l = 0 ↔ ∀ i, (poly l).coeff i = 0 :=
      ⟨fun h => by simp [h], fun h => LaurentPolynomial.ext h⟩
    simpa using he.trans (by simpa using finite_coeff (fun _ => False) l)
  rw [← plain, ← plain, ← finite_coeff, ← mask_eq_zero]
  constructor
  · intro h
    exact ⟨by simpa [readState, expVal, sub_eq_zero] using congrArg Triangular.t h,
      congrArg Triangular.x h, congrArg Triangular.y h, congrArg Triangular.z h⟩
  · rintro ⟨ht, hx, hy, hz⟩
    exact tri_ext (by simp [readState, expVal, ht]) hx hy hz

open Primrec in
private lemma pr_eadd : Primrec₂ eadd :=
  (nat_add.comp (fst.comp fst) (fst.comp snd)).pair (nat_add.comp (snd.comp fst) (snd.comp snd))

open Primrec in
private lemma pr_translate {α : Type} [Primcodable α] {i : α → Exponent} {b : α → Bool}
    {l : α → Poly} (hi : Primrec i) (hb : Primrec b) (hl : Primrec l) :
    Primrec fun a => translate (i a) (b a) (l a) := by
  exact list_map hl ((pr_eadd.comp (hi.comp fst) (fst.comp snd)).pair
    ((dom_bool₂ (· == ·)).comp (hb.comp fst) (snd.comp snd))).to₂

open Primrec in
private lemma pr_step : Primrec₂ step := by
  have hs : Primrec (fun p : State × Letter => p.1.1) := fst.comp fst
  have hi : Primrec (fun p : State × Letter => p.2.1) := fst.comp snd
  have hb : Primrec (fun p : State × Letter => p.2.2) := snd.comp snd
  have hrest : Primrec (fun p : State × Letter => p.1.2) := snd.comp fst
  have hx := fst.comp hrest
  have hyz := snd.comp hrest
  exact ite (Primrec.eq.comp hi (const 0))
    ((pr_eadd.comp hs ((dom_bool tick).comp hb)).pair hrest)
    (ite (Primrec.eq.comp hi (const 1))
      (hs.pair ((list_cons.comp (((snd.comp hs).pair (fst.comp hs)).pair hb) hx).pair hyz))
      (hs.pair (hx.pair ((list_cons.comp (hs.pair hb) (fst.comp hyz)).pair
        (list_append.comp (pr_translate hs hb hx) (snd.comp hyz))))))

private lemma pr_eval : Primrec (fun w : Word => w.foldl step start) :=
  Primrec.list_foldl .id (.const start)
    ((Primrec.comp (f := fun p : State × Letter => step p.1 p.2) pr_step Primrec.snd).to₂)

open Primrec in
private lemma pr_cnt {α : Type} [Primcodable α] {i : α → Exponent} {b : α → Bool}
    {l : α → Poly} (hi : Primrec i) (hb : Primrec b) (hl : Primrec l) :
    Primrec fun a => countTerms (i a) (b a) (l a) := by
  have he := hi.comp (fst (α := α) (β := Term × ℕ))
  have hm : Primrec (fun p : α × (Term × ℕ) => p.2.1) := fst.comp snd
  have hExp := Primrec.eq.comp (nat_add.comp (fst.comp he) (snd.comp (fst.comp hm)))
    (nat_add.comp (fst.comp (fst.comp hm)) (snd.comp he))
  exact list_foldr hl (const 0) ((ite (hExp.and (Primrec.eq.comp (hb.comp fst) (snd.comp hm)))
    (succ.comp (snd.comp snd)) (snd.comp snd)).to₂)

-- All coefficients outside the finite term list vanish. For each listed central exponent,
-- zero coefficient is decidable and membership in K is recursively enumerable.
private lemma re_words {K : ℕ → Prop} (hK : REPred K) :
    REPred fun w : Word => FreeGroup.lift (basis (P := mask K)) (FreeGroup.mk w) = 1 := by
  have hbal : PrimrecPred fun p : Poly × Term =>
      countTerms p.2.1 true p.1 = countTerms p.2.1 false p.1 :=
    Primrec.eq.comp (pr_cnt (Primrec.fst.comp .snd) (.const true) .fst)
      (pr_cnt (Primrec.fst.comp .snd) (.const false) .fst)
  have plain : REPred fun l : Poly => ∀ m ∈ l, countTerms m.1 true l = countTerms m.1 false l :=
    MetaMathlibExt.REPred.forall_mem hbal.computablePred.to_re Primrec.id
  have hk : REPred fun p : Poly × Term => K (p.2.1.1 - p.2.1.2) :=
    hK.comp (Primrec.nat_sub.comp
      (Primrec.fst.comp (Primrec.fst.comp .snd)) (Primrec.snd.comp (Primrec.fst.comp .snd))).to_comp
  have masked : REPred fun l : Poly => ∀ m ∈ l,
      K (m.1.1 - m.1.2) ∨ countTerms m.1 true l = countTerms m.1 false l :=
    MetaMathlibExt.REPred.forall_mem (R := fun (l : Poly) (m : Term) => K (m.1.1 - m.1.2) ∨
      countTerms m.1 true l = countTerms m.1 false l)
      (MetaMathlibExt.REPred.or hk hbal.computablePred.to_re) Primrec.id
  have ht : PrimrecPred fun s : State => s.1.1 = s.1.2 :=
    Primrec.eq.comp (Primrec.fst.comp .fst) (Primrec.snd.comp .fst)
  have hx : Computable (fun s : State => s.2.1) := Computable.fst.comp .snd
  have hy : Computable (fun s : State => s.2.2.1) := Computable.fst.comp (Computable.snd.comp .snd)
  have hz : Computable (fun s : State => s.2.2.2) := Computable.snd.comp (Computable.snd.comp .snd)
  apply REPred.of_eq ((MetaMathlibExt.REPred.and ht.computablePred.to_re (MetaMathlibExt.REPred.and
    (plain.comp hx) (MetaMathlibExt.REPred.and (plain.comp hy) (masked.comp hz)))).comp
      pr_eval.to_comp)
  intro w
  exact (eval_one K _).symm.trans (by rw [eval_correct])

-- Conjugating the second unipotent generator by n shifts yields the entry T n.
-- Its commutator with the first unipotent generator reads the masked central coefficient.
private def shifted (n : ℕ) : Word :=
  List.replicate n (0, true) ++ [(2, true)] ++ List.replicate n (0, false)

private def probe (n : ℕ) : Word :=
  [(1, true)] ++ shifted n ++ [(1, false)] ++ FreeGroup.invRev (shifted n)

private def diag (i : ℤ) : Triangular P := ⟨i, 0, 0, 0⟩

private lemma diag_add (i j : ℤ) : diag (P := P) (i + j) = diag i * diag j := by
  apply tri_ext <;> simp [diag]

private lemma diag_pow (i : ℤ) (n : ℕ) : (diag (P := P) i) ^ n = diag (n * i) := by
  induction n with
  | zero => apply tri_ext <;> simp [diag]
  | succ n ih => rw [pow_succ, ih, Nat.cast_succ, add_mul, one_mul, diag_add]

private lemma eval_shifted (n : ℕ) : FreeGroup.lift (basis (P := P)) (FreeGroup.mk (shifted n)) =
    ⟨0, 0, T n, 0⟩ := by
  simp only [FreeGroup.lift_mk, shifted, List.map_append, List.prod_append, List.map_replicate,
    List.prod_replicate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.cond_true, Bool.cond_false, mul_one]
  have hpos : basis (P := P) 0 = diag 1 := rfl
  have hneg : (basis (P := P) 0)⁻¹ = diag (-1) := by
    apply tri_ext <;> simp [basis, diag, Inv.inv]
  rw [hneg, hpos, diag_pow, diag_pow]
  apply tri_ext <;> simp [basis, diag, twist]

private lemma probe_iff (K : ℕ → Prop) (n : ℕ) :
    FreeGroup.lift (basis (P := mask K)) (FreeGroup.mk (probe n)) = 1 ↔ K n := by
  have he : FreeGroup.lift (basis (P := mask K)) (FreeGroup.mk (probe n)) =
      ⟨0, 0, 0, mask K (T n)⟩ := by
    simp only [probe, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv, eval_shifted]
    apply tri_ext <;> simp [FreeGroup.lift_mk, basis, Inv.inv]
  rw [he]
  have hz : (⟨0, 0, 0, mask K (T n)⟩ : Triangular (mask K)) = 1 ↔ mask K (T n) = 0 :=
    ⟨congrArg Triangular.z, fun h => tri_ext rfl rfl rfl h⟩
  rw [hz, mask_eq_zero]
  constructor
  · intro h
    simpa using h n
  · intro h i
    by_cases hi : (n : ℤ) = i
    · simpa [← hi] using Or.inl (b := False) h
    · exact Or.inr (by simp [hi])

private lemma pr_replicate (a : Letter) : Primrec fun n : ℕ => List.replicate n a := by
  simpa using Primrec.list_map Primrec.list_range (Primrec₂.const a)

open Primrec in
private lemma pr_probe : Primrec probe := by
  have hs : Primrec shifted := list_append.comp (list_append.comp (pr_replicate (0, true))
    (const [(2, true)])) (pr_replicate (0, false))
  have hinv : Primrec (FreeGroup.invRev (α := Fin 3)) :=
    list_reverse.comp (list_map .id ((fst.pair (Primrec.not.comp snd)).comp₂ Primrec₂.right))
  exact list_append.comp (list_append.comp (list_append.comp (const [(1, true)]) hs)
    (const [(1, false)])) (hinv.comp hs)

/--
**A soluble right-orderable group with insoluble word problem (Kourovka 17.28).** There exist a
soluble group $G$ that admits a right order, a natural number $k$ and elements
$g_0, \dots, g_{k-1}$ generating $G$ such that, for the homomorphism $\varphi$ from the free group
on $k$ generators to $G$ sending the $i$-th generator to $g_i$, the group $G$ is recursively
presented with respect to $\varphi$ and the word problem for $\varphi$ is not solvable.

Resolved true: Darbinyan constructs a two-generated, recursively presented, bi-orderable (hence
right-orderable) soluble group of derived length 3 with undecidable word problem; the Kourovka
Archive answers 17.28 "Yes, there is".

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved
Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of
Solved Problems, Problem 17.28 (V. V. Bludov, A. M. W. Glass); resolution: A. Darbinyan,
Computability, orders, and solvable groups, J. Symbolic Logic 85 (2020), 1588-1598
(arXiv:1909.05720), abstract, result (2) (a bi-orderable, two-generated, recursively presented
solvable group of derived length 3 with undecidable word problem, answering the question of Bludov
and Glass); Kourovka Archive, Problem 17.28 (Yes, there is), https://arxiv.org/abs/1909.05720.
-/
public theorem solubleRightOrderableInsolubleWordProblem_holds :
    solubleRightOrderableInsolubleWordProblem := by
  let K (n : ℕ) := ((Denumerable.ofNat Nat.Partrec.Code n).eval 0).Dom
  have hK : REPred K := (ComputablePred.halting_problem_re 0).comp (Primrec.ofNat _).to_comp
  have hn : ¬ ComputablePred K := by
    intro hc
    apply ComputablePred.halting_problem 0
    exact ComputablePred.computable_of_manyOneReducible ⟨Encodable.encode, Primrec.encode.to_comp,
      fun c => by simp [K]⟩ hc
  let φ := FreeGroup.lift (basis (P := mask K))
  let ψ := φ.rangeRestrict
  have hψ (w : Word) : φ (FreeGroup.mk w) = 1 ↔ ψ (FreeGroup.mk w) = 1 :=
    ⟨fun h => Subtype.ext h, congrArg Subtype.val⟩
  let gens : Fin 3 → φ.range := ψ ∘ FreeGroup.of
  have he : FreeGroup.lift gens = ψ := FreeGroup.lift.apply_symm_apply ψ
  let := LinearOrder.lift' (fun a : φ.range => coord a.val) (coord_inj.comp Subtype.val_injective)
  have : Group.IsSolvable (Triangular (mask K)) := tri_solvable
  refine ⟨φ.range, inferInstance, inferInstance, ⟨(· ≤ ·), inferInstance, ?_⟩, 3, gens,
    FreeGroup.lift_surjective_iff_closure_range_eq_top.mp (he ▸ φ.rangeRestrict_surjective), ?_, ?_⟩
  · intro a b c h
    exact coord_mono a.val b.val c.val h
  · unfold IsRecursivelyPresented
    rw [he]
    exact (re_words hK).of_eq hψ
  · intro hc
    apply hn
    change ComputablePred (fun w : Word => FreeGroup.lift gens (FreeGroup.mk w) = 1) at hc
    apply ComputablePred.computable_of_manyOneReducible _ hc
    refine ⟨probe, pr_probe.to_comp, fun n => ?_⟩
    change K n ↔ FreeGroup.lift gens (FreeGroup.mk (probe n)) = 1
    rw [he]
    exact (probe_iff K n).symm.trans (hψ _)

end

end MathlibExt.GroupTheory.SolubleRightOrderableWordProblemKourovka17Problem28Wanted
