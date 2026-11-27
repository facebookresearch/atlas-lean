/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Computability.RE
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.FiniteSupport.Basic
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FreeGroup.Reduce
import Mathlib.GroupTheory.RegularWreathProduct
import MathlibExt.Computability.RE

/-!
# Word problems for free abelianized extensions

The word problems for the quotients by a recursively enumerable normal subgroup of a finite-rank
free group and by its derived subgroup are equivalent (Kourovka Notebook Problem 12.98(a)).

A word belongs to the derived subgroup precisely when its path in the Cayley graph of the first
quotient closes and traverses each edge equally often in both directions. For the converse
reduction, a loop with a nonzero signed edge count has finite nonempty support. Elements commuting
with that loop modulo the derived subgroup preserve its support, restricting their images in the
first quotient to finitely many cosets.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted

/-!
Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E.
Shpil'rain). UnsolvedMath record UM-00700915 (`KOU-12.98`), dataset ulamai/UnsolvedMath v1.8.0.

Words over `F = F(x₀, …, x_{n-1})` are coded as `List (Fin n × Bool)`, as in
`WordProblemSolvableShared`. A recursively defined normal subgroup is a recursively enumerable one
(so `F ⧸ R` is recursively presented). The word problem for `F ⧸ N` is decidability of membership in
`N`; the conjugacy problem is decidability of `∃ u, u w u⁻¹ v⁻¹ ∈ N`, which is conjugacy in `F ⧸ N`
for normal `N`.
-/

/-- **Recursively enumerable subgroup of a free group.** Let $n$ be a natural number and let $F$
be the free group on the generators $x_0, \dots, x_{n-1}$. A subgroup $N$ of $F$ is recursively
enumerable when the set of words $w$ (finite lists of letters, each a generator together with a
sign) whose image in $F$ lies in $N$ is recursively enumerable. -/
def IsRecursivelyEnumerable {n : ℕ} (N : Subgroup (FreeGroup (Fin n))) : Prop :=
  REPred fun w : List (Fin n × Bool) => FreeGroup.mk w ∈ N

/-- **Solvable word problem for a quotient of a free group.** Let $n$ be a natural number, let $F$
be the free group on the generators $x_0, \dots, x_{n-1}$ and let $N$ be a subgroup of $F$. The word
problem for $F / N$ is solvable when membership in $N$ is decidable: the predicate on words $w$
(finite lists of letters, each a generator together with a sign) that the image of $w$ in $F$ lies
in $N$ is computable. -/
def WordProblemSolvable {n : ℕ} (N : Subgroup (FreeGroup (Fin n))) : Prop :=
  ComputablePred fun w : List (Fin n × Bool) => FreeGroup.mk w ∈ N

/-- **Solvable conjugacy problem for a quotient of a free group.** Let $n$ be a natural number,
let $F$ be the free group on the generators $x_0, \dots, x_{n-1}$ and let $N$ be a subgroup of $F$.
The conjugacy problem for $F / N$ is solvable when the predicate on pairs of words $(w, v)$ (finite
lists of letters, each a generator together with a sign) that some $u \in F$ satisfies
$u w u^{-1} v^{-1} \in N$, with $w$ and $v$ read as elements of $F$, is computable.

When $N$ is normal, this says that conjugacy of the images of $w$ and $v$ in $F / N$ is
decidable. -/
def ConjugacyProblemSolvable {n : ℕ} (N : Subgroup (FreeGroup (Fin n))) : Prop :=
  ComputablePred fun wv : List (Fin n × Bool) × List (Fin n × Bool) =>
    ∃ u : FreeGroup (Fin n), u * FreeGroup.mk wv.1 * u⁻¹ * (FreeGroup.mk wv.2)⁻¹ ∈ N

/-- **Kourovka Problem 12.98(a) (V. E. Shpil'rain).** The statement that for every natural
number $n$ and every recursively enumerable normal subgroup $R$ of the free group $F$ on $n$
generators, with commutator subgroup $[R, R]$, the word problem for $F / R$ is solvable if and only
if the word problem for $F / [R, R]$ is solvable. -/
def wordProblemIffMetabelianization : Prop :=
  ∀ (n : ℕ) (R : Subgroup (FreeGroup (Fin n))), R.Normal → IsRecursivelyEnumerable R →
    (WordProblemSolvable R ↔ WordProblemSolvable ⁅R, R⁆)

private abbrev Word (n : ℕ) := List (Fin n × Bool)
private abbrev Edge (n : ℕ) := Word n × Fin n × Bool

variable {n : ℕ}
variable (R : Subgroup (FreeGroup (Fin n))) [R.Normal]
private abbrev Vertex := FreeGroup (Fin n) ⧸ R
private abbrev q := QuotientGroup.mk' R
private def vertex (p : Word n) := q R (FreeGroup.mk p)

private theorem vertex_append (p l : Word n) :
    vertex R (p ++ l) = vertex R p * vertex R l := by
  exact map_mul (q R) (FreeGroup.mk p) (FreeGroup.mk l)

private theorem vertex_pos (i : Fin n) : vertex R [(i, true)] = q R (FreeGroup.of i) := rfl

private theorem vertex_neg (i : Fin n) : vertex R [(i, false)] = (q R (FreeGroup.of i))⁻¹ :=
  map_inv (q R) (FreeGroup.of i)

-- Record each oriented edge by a word for the initial vertex of its positive orientation.
private def edges (p : Word n) : Word n → List (Edge n)
  | [] => []
  | a :: l => ((if a.2 then p else p ++ [a]), a) :: edges (p ++ [a]) l

private def signProd {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A)
    (s : List (Edge n)) :=
  (s.map fun (p, i, b) => cond b (f (vertex R p, i)) (f (vertex R p, i))⁻¹).prod

private theorem signProd_cons {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A)
    (p : Word n) (i : Fin n) (b : Bool) (s : List (Edge n)) :
    signProd R f ((p, i, b) :: s) =
      cond b (f (vertex R p, i)) (f (vertex R p, i))⁻¹ * signProd R f s := rfl

-- Wreath product coordinates evaluate a path with any abelian labelling of its edges.
private def walk {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A) :
    FreeGroup (Fin n) →* A ≀ᵣ Vertex R :=
  FreeGroup.lift fun i => RegularWreathProduct.mk (fun x => f (x⁻¹, i)) (q R (FreeGroup.of i))

private theorem walk_right {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A)
    (x : FreeGroup (Fin n)) : (walk R f x).right = q R x := by
  have h : RegularWreathProduct.rightHom.comp (walk R f) = q R := by
    apply FreeGroup.ext_hom
    intro i
    simp [walk]
  exact DFunLike.congr_fun h x

private theorem walk_edges {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A)
    (l p : Word n) :
    (walk R f (FreeGroup.mk l)).left (vertex R p)⁻¹ = signProd R f (edges p l) := by
  induction l generalizing p with
  | nil => change (walk R f 1).left _ = 1; simp
  | cons a l ih =>
    obtain ⟨i, b⟩ := a
    rw [show FreeGroup.mk ((i, b) :: l) = FreeGroup.mk [(i, b)] * FreeGroup.mk l from rfl]
    cases b <;>
      simp only [map_mul, RegularWreathProduct.mul_left, Pi.mul_apply, edges, signProd_cons,
        Bool.false_eq_true, ite_false, ite_true, Bool.cond_false, Bool.cond_true, ← ih,
        vertex_append, vertex_pos, vertex_neg, FreeGroup.mk_eq_inv_of, FreeGroup.mk_eq_of,
        walk, map_inv, FreeGroup.lift_apply_of, RegularWreathProduct.inv_left,
        RegularWreathProduct.inv_right, Pi.inv_apply, mul_inv_rev, inv_inv]

private theorem derived_le_ker_walk {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A) :
    ⁅R, R⁆ ≤ (walk R f).ker := by
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
  have hx' : (walk R f x).right = 1 := (walk_right ..).trans ((QuotientGroup.eq_one_iff _).2 hx)
  have hy' : (walk R f y).right = 1 := (walk_right ..).trans ((QuotientGroup.eq_one_iff _).2 hy)
  ext z <;> simp [hx', hy', mul_comm]

private abbrev posKeys (b : Bool) (s : List (Edge n)) : List (Vertex R × Fin n) :=
  (s.filter fun e => e.2.2 == b).map fun e => (vertex R e.1, e.2.1)

private theorem signProd_split {A : Type*} [CommGroup A] (f : Vertex R × Fin n → A)
    (s : List (Edge n)) :
    signProd R f s = ((posKeys R true s).map f).prod / ((posKeys R false s).map f).prod := by
  induction s with
  | nil => simp [signProd]
  | cons e s ih =>
    obtain ⟨p, i, b⟩ := e
    cases b <;> simp only [signProd_cons, Bool.cond_false, Bool.cond_true, ih,
      posKeys, List.filter_cons, beq_self_eq_true, Bool.true_beq, Bool.false_beq, Bool.not_true,
      Bool.false_eq_true, ite_false, ite_true, List.map_cons, List.prod_cons, div_eq_mul_inv,
      mul_inv_rev]
    · exact (mul_comm ..).trans (mul_assoc ..)
    · exact (mul_assoc ..).symm

-- Mark a single quotient edge to read off its signed count.
open scoped Classical in
private noncomputable def mark {K : Type*} (k e : K) : Multiplicative ℤ :=
  if e = k then Multiplicative.ofAdd 1 else 1

private theorem count_label {K : Type*} [DecidableEq K] (k : K) (s : List K) :
    (s.map (mark k)).prod = Multiplicative.ofAdd (s.count k : ℤ) := by
  induction s with
  | nil => rfl
  | cons e s ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases he : e = k
    · subst e
      simp [mark, ← ofAdd_add, add_comm]
    · simp [mark, he]

private theorem marked_one_iff [DecidableEq (Vertex R × Fin n)] (k : Vertex R × Fin n)
    (l : Word n) : (walk R (mark k) (FreeGroup.mk l)).left 1 = 1 ↔
      (posKeys R true (edges [] l)).count k = (posKeys R false (edges [] l)).count k := by
  have h := walk_edges R (mark k) l []
  have hv : vertex R [] = 1 := rfl
  rw [hv, inv_one, signProd_split, count_label, count_label] at h
  rw [h, div_eq_one]
  exact ⟨fun e => by exact_mod_cast Multiplicative.ofAdd.injective e, fun e => by rw [e]⟩

private theorem balanced_of_derived (l : Word n) (hl : FreeGroup.mk l ∈ ⁅R, R⁆) :
    (posKeys R true (edges [] l)).Perm (posKeys R false (edges [] l)) := by
  classical
  apply List.perm_iff_count.mpr
  intro k
  apply (marked_one_iff R k l).mp
  have hw : walk R (mark k) (FreeGroup.mk l) = 1 := derived_le_ker_walk R (mark k) hl
  rw [hw]
  rfl

-- A section of the quotient turns each edge into a loop in R. The factors telescope.
private noncomputable def rep (g : Vertex R) : FreeGroup (Fin n) :=
  (QuotientGroup.mk'_surjective R g).choose

private theorem q_rep (g : Vertex R) : (rep R g : Vertex R) = g :=
  (QuotientGroup.mk'_surjective R g).choose_spec

private noncomputable def loopAt (g : Vertex R) (x : FreeGroup (Fin n)) : R :=
  ⟨rep R g * x * (rep R (g * q R x))⁻¹, (QuotientGroup.eq_one_iff _).mp (by simp [q_rep])⟩

private theorem loopAt_mul (g : Vertex R) (x y : FreeGroup (Fin n)) :
    loopAt R g (x * y) = loopAt R g x * loopAt R (g * q R x) y := by
  ext
  simp [loopAt, mul_assoc]

private theorem signProd_loops (l p : Word n) :
    signProd R (fun (g, i) => Group.Abelianization.of (loopAt R g (FreeGroup.of i))) (edges p l) =
      Group.Abelianization.of (loopAt R (vertex R p) (FreeGroup.mk l)) := by
  induction l generalizing p with
  | nil =>
    have h : loopAt R (vertex R p) 1 = 1 := by ext; simp [loopAt]
    change 1 = Group.Abelianization.of (loopAt R _ 1)
    rw [h, map_one]
  | cons a l ih =>
    obtain ⟨i, b⟩ := a
    rw [show FreeGroup.mk ((i, b) :: l) = FreeGroup.mk [(i, b)] * FreeGroup.mk l from rfl,
      loopAt_mul, map_mul]
    cases b
    · have hi : (loopAt R (vertex R (p ++ [(i, false)])) (FreeGroup.of i))⁻¹ =
          loopAt R (vertex R p) (FreeGroup.of i)⁻¹ := by
        ext
        simp [loopAt, vertex_append, vertex_neg, mul_assoc]
      simp only [edges, signProd_cons, Bool.false_eq_true, ite_false, Bool.cond_false,
        ih, vertex_append, vertex_neg, FreeGroup.mk_eq_inv_of, map_inv]
      rw [vertex_append, vertex_neg] at hi
      rw [← map_inv, hi]
    · simpa [edges, signProd, vertex_append, vertex_pos, FreeGroup.mk_eq_of] using congrArg
        (fun y => Group.Abelianization.of (loopAt R (vertex R p) (FreeGroup.of i)) * y)
        (ih (p ++ [(i, true)]))

private theorem derived_iff (l : Word n) :
    FreeGroup.mk l ∈ ⁅R, R⁆ ↔ FreeGroup.mk l ∈ R ∧
      (posKeys R true (edges [] l)).Perm (posKeys R false (edges [] l)) := by
  constructor
  · exact fun h => ⟨Subgroup.commutator_le_self R h, balanced_of_derived R l h⟩
  rintro ⟨hl, hperm⟩
  let f (e : Vertex R × Fin n) := Group.Abelianization.of (loopAt R e.1 (FreeGroup.of e.2))
  have h := (signProd_loops R l []).symm
  rw [signProd_split, div_eq_one.mpr (hperm.map f).prod_eq] at h
  have hmem : loopAt R (vertex R []) (FreeGroup.mk l) ∈ commutator R := by
    rwa [← Group.Abelianization.ker_of, MonoidHom.mem_ker]
  have hmap := Subgroup.mem_map_of_mem R.subtype hmem
  rw [R.map_subtype_commutator] at hmap
  have hq : q R (FreeGroup.mk l) = 1 := (QuotientGroup.eq_one_iff _).mpr hl
  change rep R _ * FreeGroup.mk l * (rep R (_ * q R (FreeGroup.mk l)))⁻¹ ∈ ⁅R, R⁆ at hmap
  rw [hq, mul_one] at hmap
  simpa [mul_assoc] using (inferInstance : (⁅R, R⁆).Normal).mem_comm hmap

private theorem prim_invRev : Primrec (FreeGroup.invRev (α := Fin n)) :=
  Primrec.list_reverse.comp (Primrec.list_map .id
    ((Primrec.fst.comp Primrec.snd).pair (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂)

private theorem comp_pre {X Y : Type*} [Primcodable X] [Primcodable Y] {P : Y → Prop}
    {f : X → Y} (h : ComputablePred P) (hf : Computable f) :
    ComputablePred fun x => P (f x) := by
  classical
  exact (h.decide.comp hf).computablePred

private theorem comp_vertex_eq (hR : WordProblemSolvable R) :
    ComputablePred fun p : Word n × Word n => vertex R p.1 = vertex R p.2 := by
  apply (comp_pre hR (Primrec.list_append.comp Primrec.fst
    (prim_invRev.comp Primrec.snd)).to_comp).of_eq
  intro p
  rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, ← div_eq_mul_inv]
  exact QuotientGroup.eq_iff_div_mem.symm

private theorem prim_edges : Primrec (edges ([] : Word n)) := by
  let step (s : Word n × List (Edge n)) (a : Fin n × Bool) : Word n × List (Edge n) :=
    (s.1 ++ [a], ((if a.2 then s.1 else s.1 ++ [a]), a) :: s.2)
  have hs : Primrec₂ step := by
    have hnext : Primrec fun v : (Word n × List (Edge n)) × (Fin n × Bool) => v.1.1 ++ [v.2] :=
      Primrec.list_concat.comp (Primrec.fst.comp Primrec.fst) Primrec.snd
    apply Primrec.pair hnext
    apply Primrec.list_cons.comp _ (Primrec.snd.comp Primrec.fst)
    apply Primrec.pair _ Primrec.snd
    exact (Primrec.cond (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.fst)
      hnext).of_eq fun v => by cases v.2.2 <;> rfl
  have scan (l : Word n) (v : Word n × List (Edge n)) :
      (l.foldl step v).2.reverse = v.2.reverse ++ edges v.1 l := by
    induction l generalizing v with
    | nil => simp [edges]
    | cons a l ih => simp [List.foldl_cons, ih, step, edges]
  apply (Primrec.list_reverse.comp (Primrec.snd.comp (Primrec.list_foldl Primrec.id
    (Primrec.const (([], []) : Word n × List (Edge n))) (Primrec.comp hs Primrec.snd).to₂))).of_eq
  intro l
  exact (scan l ([], []))

-- Count the occurrences passing a computable test by scanning the given list.
private theorem comp_countP {X Y : Type*} [Primcodable X] [Primcodable Y]
    {l : X → List Y} {p : X → Y → Bool} (hl : Computable l) (hp : Computable₂ p) :
    Computable fun x => (l x).countP (p x) := by
  let addAt (x : X) (s : ℕ × ℕ) :=
    s.2 + (((l x)[s.1]?).elim 0 fun y => cond (p x y) 1 0)
  have ha : Computable₂ addAt := by
    apply Primrec.nat_add.to_comp.comp (Computable.snd.comp Computable.snd)
    apply (Computable.option_casesOn
      (Computable.list_getElem?.comp (hl.comp Computable.fst) (Computable.fst.comp Computable.snd))
      (Computable.const 0) ((hp.comp (Computable.fst.comp Computable.fst)
        Computable.snd).cond (Computable.const 1) (Computable.const 0)).to₂).of_eq
    intro s
    cases (l s.1)[s.2.1]? <;> rfl
  apply (Computable.nat_rec (h := addAt) (Computable.list_length.comp hl)
    (Computable.const 0) ha).of_eq
  intro x
  suffices ∀ k ≤ (l x).length, Nat.rec 0 (fun i acc => addAt x (i, acc)) k =
      ((l x).take k).countP (p x) by simpa using this _ le_rfl
  intro k
  induction k with
  | zero => simp
  | succ i ih =>
    intro hi
    have h : i < (l x).length := hi
    change addAt x (i, _) = _
    rw [ih (Nat.le_of_lt h)]
    simp only [addAt, List.take_succ_eq_append_getElem h,
      List.getElem?_eq_getElem h, Option.elim_some, List.countP_append, List.countP_cons,
      List.countP_nil, Nat.zero_add, Bool.cond_eq_ite]

private def key (e : Edge n) := (vertex R e.1, e.2.1)

private theorem comp_balanced (hR : WordProblemSolvable R) :
    ComputablePred fun l : Word n =>
      (posKeys R true (edges [] l)).Perm (posKeys R false (edges [] l)) := by
  classical
  have heq : ComputablePred fun u : Edge n × Edge n => key R u.1 = key R u.2 := by
    apply (MetaMathlibExt.ComputablePred.and
      (comp_pre (comp_vertex_eq R hR) ((Primrec.fst.comp Primrec.fst).pair
        (Primrec.fst.comp Primrec.snd)).to_comp)
      (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).computablePred).of_eq
    intro u
    exact Prod.mk.injEq .. |>.to_iff.symm
  have hc (b : Bool) : Computable fun v : Word n × Edge n =>
      (posKeys R b (edges [] v.1)).count (key R v.2) := by
    refine (comp_countP (prim_edges.to_comp.comp Computable.fst) (p := fun v e =>
      decide (key R e = key R v.2) && (e.2.2 == b)) ?_).of_eq ?_
    · change Computable fun u : (Word n × Edge n) × Edge n =>
        decide (key R u.2 = key R u.1.2) && (u.2.2.2 == b)
      have ht : ComputablePred fun u : (Word n × Edge n) × Edge n => key R u.2 = key R u.1.2 :=
        comp_pre heq (Computable.snd.pair (Computable.snd.comp Computable.fst))
      exact Primrec.and.to_comp.comp ht.decide
        (Primrec.beq.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.const b)).to_comp
    · intro v
      simp only [posKeys, List.count_eq_countP, List.countP_map, List.countP_filter,
        Function.comp_def, beq_eq_decide]
      congr 1
  have test := MetaMathlibExt.computable_list_any prim_edges.to_comp
    (Primrec.not.to_comp.comp (Primrec.beq.to_comp.comp (hc true) (hc false))).to₂
  let bad (l : Word n) := (edges [] l).any fun e =>
    !((posKeys R true (edges [] l)).count (key R e) ==
      (posKeys R false (edges [] l)).count (key R e))
  have hbad : ComputablePred fun l => bad l = true :=
    ComputablePred.computable_iff.mpr ⟨bad, test, rfl⟩
  apply hbad.not.of_eq
  intro l
  simp only [bad, List.any_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, not_exists, not_and,
    not_not]
  rw [List.perm_iff_count]
  constructor
  · intro h k
    by_cases hk : ∃ e ∈ edges [] l, key R e = k
    · obtain ⟨e, he, rfl⟩ := hk
      exact h e he
    · have hz (b : Bool) : k ∉ posKeys R b (edges [] l) := by
        simp only [posKeys, List.mem_map, List.mem_filter]
        rintro ⟨e, ⟨he, -⟩, h⟩
        exact hk ⟨e, he, h⟩
      simp [List.count_eq_zero.mpr (hz true), List.count_eq_zero.mpr (hz false)]
  · exact fun h e _ => h (key R e)

open scoped commutatorElement
open Function

private theorem finite_walk (k : Vertex R × Fin n) (x : FreeGroup (Fin n)) :
    ((walk R (mark k) x).left).HasFiniteMulSupport := by
  classical
  induction x using FreeGroup.induction_on with
  | one => simpa using (hasFiniteMulSupport_fun_one (α := Vertex R)
      (M := Multiplicative ℤ))
  | of i =>
    simp only [walk, FreeGroup.lift_apply_of]
    apply (Set.finite_singleton k.1⁻¹).subset
    intro g hg
    change mark k (g⁻¹, i) ≠ 1 at hg
    by_contra h
    exact hg (ite_eq_right (fun he => h (by
      change g = k.1⁻¹
      simpa using congrArg (fun e => (Prod.fst e)⁻¹) he)))
  | inv_of i ih =>
    rw [map_inv, RegularWreathProduct.inv_left]
    exact ih.inv.fun_comp_of_injective
      (mul_right_injective (walk R (mark k) (FreeGroup.of i)).right)
  | mul x y hx hy =>
    rw [map_mul]
    exact hx.mul (hy.fun_comp_of_injective (mul_right_injective _))

private theorem re_vertex_mem (hR : IsRecursivelyEnumerable R)
    (s : Finset (Vertex R)) : REPred fun w : Word n => vertex R w ∈ s := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ((Primrec.const false).to_comp.computablePred (p := fun _ : Word n => False)).to_re.of_eq
      fun _ => by simp
  | insert g s _ ih =>
    have hg : REPred fun w : Word n => vertex R w = g := by
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective R g
      let v := FreeGroup.invRev x.toWord
      have hc : Computable fun w : Word n => w ++ v :=
        Primrec.list_append.to_comp.comp Computable.id (Computable.const v)
      have hh : REPred fun w : Word n => FreeGroup.mk (w ++ v) ∈ R := Partrec.comp hR hc
      apply hh.of_eq
      intro w
      change FreeGroup.mk (w ++ FreeGroup.invRev x.toWord) ∈ R ↔ _
      rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, FreeGroup.mk_toWord, ← div_eq_mul_inv]
      exact QuotientGroup.eq_iff_div_mem.symm
    exact (MetaMathlibExt.REPred.or hg ih).of_eq fun _ => Finset.mem_insert.symm

omit [R.Normal] in
private theorem comp_comm_test (hD : WordProblemSolvable ⁅R, R⁆) (r : Word n) :
    ComputablePred fun w : Word n => ⁅FreeGroup.mk w, FreeGroup.mk r⁆ ∈ ⁅R, R⁆ := by
  apply (comp_pre hD (Primrec.list_append.comp
    (Primrec.list_append.comp (Primrec.list_append.comp Primrec.id (Primrec.const r)) prim_invRev)
    (Primrec.const (FreeGroup.invRev r))).to_comp).of_eq
  intro w
  simp only [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, commutatorElement_def, id_eq]

private theorem word_of_derived (hR : IsRecursivelyEnumerable R) (hD : WordProblemSolvable ⁅R, R⁆) :
    WordProblemSolvable R := by
  classical
  by_cases hle : R ≤ ⁅R, R⁆
  · rwa [le_antisymm hle (Subgroup.commutator_le_self R)]
  obtain ⟨x, hx, hx'⟩ := IsConcreteLE.not_le_iff_exists.mp hle
  let r := x.toWord
  have hr : FreeGroup.mk r ∈ R := by simpa [r, FreeGroup.mk_toWord] using hx
  have hd : FreeGroup.mk r ∉ ⁅R, R⁆ := by simpa [r, FreeGroup.mk_toWord] using hx'
  have hperm := fun h => hd ((derived_iff R r).mpr ⟨hr, h⟩)
  rw [List.perm_iff_count] at hperm
  obtain ⟨k, hk⟩ := not_forall.mp hperm
  let φ := walk R (mark k)
  have hne : (φ (FreeGroup.mk r)).left 1 ≠ 1 := fun h => hk ((marked_one_iff R k r).mp h)
  -- Commuting with this loop modulo the derived subgroup forces the inverse endpoint
  -- into its finite support. Enumerate the nonidentity cosets in that support.
  let s := ((finite_walk R k (FreeGroup.mk r)).toFinset.image (·⁻¹)).erase 1
  have cover (w : Word n) (hc : ⁅FreeGroup.mk w, FreeGroup.mk r⁆ ∈ ⁅R, R⁆)
      (hw : FreeGroup.mk w ∉ R) : vertex R w ∈ s := by
    have hh : φ ⁅FreeGroup.mk w, FreeGroup.mk r⁆ = 1 := derived_le_ker_walk R (mark k) hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hh
    have hz := congrArg (fun z => RegularWreathProduct.left z 1) hh
    have hr' : (φ (FreeGroup.mk r)).right = 1 :=
      (walk_right ..).trans ((QuotientGroup.eq_one_iff _).mpr hr)
    simp only [RegularWreathProduct.mul_left, Pi.mul_apply, hr', inv_one, mul_one, one_mul] at hz
    have heq : (φ (FreeGroup.mk r)).left (vertex R w)⁻¹ = (φ (FreeGroup.mk r)).left 1 := by
      rw [mul_comm] at hz
      simpa only [mul_left_inj, φ, walk_right, vertex] using hz
    refine Finset.mem_erase.mpr ⟨fun h => hw ((QuotientGroup.eq_one_iff _).mp h), ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨(vertex R w)⁻¹, (finite_walk R k (FreeGroup.mk r)).mem_toFinset.mpr ?_, inv_inv _⟩
    exact fun h => hne (heq.symm.trans h)
  apply ComputablePred.computable_iff_re_compl_re'.mpr ⟨hR, ?_⟩
  apply (MetaMathlibExt.REPred.or (comp_comm_test R hD r).not.to_re (re_vertex_mem R hR s)).of_eq
  intro w
  constructor
  · rintro (h | h) hw
    · exact h (Subgroup.commutator_mem_commutator hw hr)
    · exact (Finset.mem_erase.mp h).1 ((QuotientGroup.eq_one_iff _).mpr hw)
  · intro hw
    by_cases hc : ⁅FreeGroup.mk w, FreeGroup.mk r⁆ ∈ ⁅R, R⁆
    · exact Or.inr (cover w hc hw)
    · exact Or.inl hc

/--
**Kourovka 12.98(a) has a positive answer.** For every natural number $n$ and every recursively
enumerable normal subgroup $R$ of the free group $F$ on $n$ generators, with commutator subgroup
$[R, R]$, the word problem for $F / R$ is solvable if and only if the word problem for $F / [R, R]$
is solvable.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 12.98 (V. E.
Shpil'rain); resolution: M. I. Anokhin, Math. Notes 61 (1997), no. 1-2, 3-8, Kourovka Archive,
Problem 12.98: a) Yes, it is; b) No, it is not; c) No, it is not.
-/
theorem wordProblemIffMetabelianization_holds : wordProblemIffMetabelianization := by
  intro n R hN hR
  constructor
  · intro h
    exact (MetaMathlibExt.ComputablePred.and h (comp_balanced R h)).of_eq
      fun w => (derived_iff R w).symm
  · exact word_of_derived R hR

end MathlibExt.GroupTheory.MetabelianizationDecisionProblemsKourovka12Problem98Wanted
