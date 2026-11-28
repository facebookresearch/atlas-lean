/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Logic.Diophantine
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Ring.IsFormallyReal

/-!
# Closure properties of Diophantine sets

Diophantine sets (`MetaMathlibExt.IsDiophantine`) over a commutative ring $R$ with coefficients
from $A$ are closed under the usual operations of positive-existential logic:

* `MetaMathlibExt.isDiophantine_of_finite`: any finite type of auxiliary variables and any finite
  family of polynomials may be used in place of `Fin n` and a `Finset`;
* `MetaMathlibExt.isDiophantine_setOf_forall_eval₂_eq_zero`: zero sets of finitely many
  polynomials, with no auxiliary variables;
* `MetaMathlibExt.IsDiophantine.inter` and, over a ring without zero divisors,
  `MetaMathlibExt.IsDiophantine.union`;
* `MetaMathlibExt.IsDiophantine.preimage_eval₂`: preimages under polynomial maps, in particular
  under coordinate maps $x \mapsto x \circ \sigma$ (`MetaMathlibExt.IsDiophantine.comp`);
* `MetaMathlibExt.IsDiophantine.image_eval₂`: images under polynomial maps, in particular
  projections (`MetaMathlibExt.IsDiophantine.exists_proj`);
* over a formally real ring (for instance a linearly ordered ring such as $\mathbb{Q}$), one
  polynomial suffices (`MetaMathlibExt.IsDiophantine.iff_single`), and
  over a field, $\{x \mid x_i \neq 0\}$ is Diophantine
  (`MetaMathlibExt.isDiophantine_setOf_ne_zero`).

Reference: B. Poonen, "Hilbert's tenth problem over rings of number-theoretic interest", notes
for the Arizona Winter School 2003, https://math.mit.edu/~poonen/papers/aws2003.pdf, Sections 6
and 8.
-/

set_option autoImplicit false

@[expose] public section

namespace MetaMathlibExt

open MvPolynomial

universe u v

variable {A : Type u} {R : Type v} [CommRing A] [CommRing R]

/-- **Diophantine sets with finitely many auxiliary variables of any type.** Let
$\varphi : A \to R$ be a ring homomorphism of commutative rings, let $\iota$ and $\kappa$ be
finite types and let $(p_j)_{j \in \kappa}$ be polynomials with coefficients in $A$ in the
variables $x_1, \dots, x_k$ and $(y_i)_{i \in \iota}$. If $S \subseteq R^k$ consists exactly of
the $x$ for which there is $y \in R^\iota$ with $p_j(x, y) = 0$ for all $j$, then $S$ is
Diophantine over $R$ with coefficients from $A$ through $\varphi$.

The auxiliary variables are renamed along a bijection $\iota \simeq \{0, \dots, n - 1\}$ and the
family is replaced by its finite set of values. -/
theorem isDiophantine_of_finite (φ : A →+* R) {k : ℕ} {S : Set (Fin k → R)} {ι κ : Type*}
    [Finite ι] [Finite κ] (p : κ → MvPolynomial (Fin k ⊕ ι) A)
    (h : ∀ x : Fin k → R, x ∈ S ↔ ∃ y : ι → R, ∀ j, eval₂ φ (Sum.elim x y) (p j) = 0) :
    IsDiophantine φ S := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let e := Fintype.equivFin ι
  refine ⟨Fintype.card ι, Finset.univ.image fun j => rename (Sum.map id e) (p j), fun x => ?_⟩
  simp only [Finset.mem_image, Finset.mem_univ, true_and, forall_exists_index,
    forall_apply_eq_imp_iff, eval₂_rename, Sum.elim_comp_map, Function.comp_id, h]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨y ∘ e.symm, fun j => ?_⟩
    rw [Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id]
    exact hy j
  · rintro ⟨y, hy⟩
    exact ⟨y ∘ e, hy⟩

/-- **Unfolding a Diophantine set into a finite family.** If $S \subseteq R^k$ is Diophantine
over $R$ with coefficients from $A$ through $\varphi$, then there are $n \in \mathbb{N}$, a finite
type $\kappa$ and polynomials $(p_j)_{j \in \kappa}$ with coefficients in $A$ in the variables
$x_1, \dots, x_k, y_1, \dots, y_n$ such that $x \in S$ if and only if $p_j(x, y) = 0$ for all $j$
and some $y \in R^n$. This is the converse of `MetaMathlibExt.isDiophantine_of_finite`, with
$\kappa$ the subtype of the given finite set of polynomials. -/
theorem IsDiophantine.exists_family {φ : A →+* R} {k : ℕ} {S : Set (Fin k → R)}
    (hS : IsDiophantine φ S) :
    ∃ (n : ℕ) (κ : Type u) (_ : Fintype κ) (p : κ → MvPolynomial (Fin k ⊕ Fin n) A),
      ∀ x : Fin k → R, x ∈ S ↔ ∃ y : Fin n → R, ∀ j, eval₂ φ (Sum.elim x y) (p j) = 0 := by
  obtain ⟨n, P, hP⟩ := hS
  exact ⟨n, P, inferInstance, Subtype.val, fun x => by simp [hP]⟩

/-- **Zero sets of finitely many polynomials are Diophantine.** Let $\varphi : A \to R$ be a ring
homomorphism of commutative rings and let $P$ be a finite set of polynomials with coefficients in
$A$ in the variables $x_1, \dots, x_k$. The set of $x \in R^k$ with $p(x) = 0$ for all $p \in P$
is Diophantine over $R$ with coefficients from $A$ through $\varphi$, with no auxiliary
variables. -/
theorem isDiophantine_setOf_forall_eval₂_eq_zero (φ : A →+* R) {k : ℕ}
    (P : Finset (MvPolynomial (Fin k) A)) :
    IsDiophantine φ {x : Fin k → R | ∀ p ∈ P, eval₂ φ x p = 0} := by
  refine isDiophantine_of_finite φ (ι := Fin 0) (fun p : P => rename Sum.inl p.1) fun x => ?_
  simp only [eval₂_rename, Sum.elim_comp_inl, Subtype.forall, Set.mem_ofPred_eq]
  exact ⟨fun h => ⟨Fin.elim0, h⟩, fun ⟨_, h⟩ => h⟩

/-- **The zero set of one polynomial is Diophantine.** Let $\varphi : A \to R$ be a ring
homomorphism of commutative rings and let $p$ be a polynomial with coefficients in $A$ in the
variables $x_1, \dots, x_k$. The set of $x \in R^k$ with $p(x) = 0$ is Diophantine over $R$ with
coefficients from $A$ through $\varphi$. -/
theorem isDiophantine_setOf_eval₂_eq_zero (φ : A →+* R) {k : ℕ} (p : MvPolynomial (Fin k) A) :
    IsDiophantine φ {x : Fin k → R | eval₂ φ x p = 0} := by
  classical
  simpa using isDiophantine_setOf_forall_eval₂_eq_zero (R := R) φ {p}

/-- **Intersections of Diophantine sets are Diophantine.** Let $\varphi : A \to R$ be a ring
homomorphism of commutative rings. If $S, T \subseteq R^k$ are Diophantine over $R$ with
coefficients from $A$ through $\varphi$, then so is $S \cap T$.

The two systems are joined with disjoint sets of auxiliary variables.

Source: B. Poonen, "Hilbert's tenth problem over rings of number-theoretic interest" (2003),
Remark 8.4, p. 7: "The collection of positive existential subsets of $R^n$ is closed under finite
unions and intersections." -/
theorem IsDiophantine.inter {φ : A →+* R} {k : ℕ} {S T : Set (Fin k → R)}
    (hS : IsDiophantine φ S) (hT : IsDiophantine φ T) : IsDiophantine φ (S ∩ T) := by
  obtain ⟨n, κ, _, p, hp⟩ := hS.exists_family
  obtain ⟨m, κ', _, q, hq⟩ := hT.exists_family
  refine isDiophantine_of_finite φ (ι := Fin n ⊕ Fin m)
    (Sum.elim (fun j => rename (Sum.map id Sum.inl) (p j))
      (fun j => rename (Sum.map id Sum.inr) (q j))) fun x => ?_
  simp only [Set.mem_inter_iff, hp, hq, Sum.forall, Sum.elim_inl, Sum.elim_inr, eval₂_rename,
    Sum.elim_comp_map, Function.comp_id]
  exact ⟨fun ⟨⟨y, hy⟩, ⟨z, hz⟩⟩ => ⟨Sum.elim y z, hy, hz⟩,
    fun ⟨w, hy, hz⟩ => ⟨⟨_, hy⟩, ⟨_, hz⟩⟩⟩

/-- **Unions of Diophantine sets are Diophantine over a ring without zero divisors.** Let
$\varphi : A \to R$ be a ring homomorphism of commutative rings, where $R$ has no zero divisors.
If $S, T \subseteq R^k$ are Diophantine over $R$ with coefficients from $A$ through $\varphi$,
then so is $S \cup T$. Nontriviality of $R$ is not needed.

The system for $S \cup T$ consists of the products $p \cdot q$ of a polynomial $p$ of the system
for $S$ and a polynomial $q$ of the system for $T$, in disjoint sets of auxiliary variables.

Source: B. Poonen, "Hilbert's tenth problem over rings of number-theoretic interest" (2003),
Remark 8.4, p. 7: "The collection of positive existential subsets of $R^n$ is closed under finite
unions and intersections", and the proof of Proposition 8.5, p. 7: "Transform each disjunction of
polynomial equations $(p = 0) \vee (q = 0)$ to $g(p, q) = 0$", here with $g(x, y) = xy$. -/
theorem IsDiophantine.union [NoZeroDivisors R] {φ : A →+* R} {k : ℕ} {S T : Set (Fin k → R)}
    (hS : IsDiophantine φ S) (hT : IsDiophantine φ T) : IsDiophantine φ (S ∪ T) := by
  classical
  obtain ⟨n, κ, _, p, hp⟩ := hS.exists_family
  obtain ⟨m, κ', _, q, hq⟩ := hT.exists_family
  refine isDiophantine_of_finite φ (ι := Fin n ⊕ Fin m)
    (fun j : κ × κ' => rename (Sum.map id Sum.inl) (p j.1) * rename (Sum.map id Sum.inr) (q j.2))
    fun x => ?_
  simp only [Set.mem_union, hp, hq, Prod.forall, eval₂_mul, eval₂_rename, Sum.elim_comp_map,
    Function.comp_id, mul_eq_zero]
  constructor
  · rintro (⟨y, hy⟩ | ⟨z, hz⟩)
    · exact ⟨Sum.elim y 0, fun i _ => Or.inl (hy i)⟩
    · exact ⟨Sum.elim 0 z, fun _ j => Or.inr (hz j)⟩
  · rintro ⟨w, h⟩
    set y := w ∘ Sum.inl
    set z := w ∘ Sum.inr
    by_cases hy : ∀ i, eval₂ φ (Sum.elim x y) (p i) = 0
    · exact Or.inl ⟨y, hy⟩
    · push Not at hy
      obtain ⟨i, hi⟩ := hy
      exact Or.inr ⟨z, fun j => (h i j).resolve_left hi⟩

/-- **Preimages of Diophantine sets under polynomial maps are Diophantine.** Let
$\varphi : A \to R$ be a ring homomorphism of commutative rings, let $T \subseteq R^k$ be
Diophantine over $R$ with coefficients from $A$ through $\varphi$, and let $f_1, \dots, f_k$ be
polynomials with coefficients in $A$ in $k'$ variables. Then
$\{x \in R^{k'} \mid (f_1(x), \dots, f_k(x)) \in T\}$ is Diophantine over $R$ with coefficients
from $A$ through $\varphi$.

The system for $T$ is composed with $f$ (`MvPolynomial.bind₁`). -/
theorem IsDiophantine.preimage_eval₂ {φ : A →+* R} {k k' : ℕ} {T : Set (Fin k → R)}
    (hT : IsDiophantine φ T) (f : Fin k → MvPolynomial (Fin k') A) :
    IsDiophantine φ {x : Fin k' → R | (fun i => eval₂ φ x (f i)) ∈ T} := by
  obtain ⟨n, κ, _, p, hp⟩ := hT.exists_family
  refine isDiophantine_of_finite φ (ι := Fin n)
    (fun j => bind₁ (Sum.elim (fun i => rename Sum.inl (f i)) (fun i => X (Sum.inr i))) (p j))
    fun x => ?_
  have key : ∀ (y : Fin n → R) (j : κ),
      eval₂ φ (Sum.elim x y)
          (bind₁ (Sum.elim (fun i => rename Sum.inl (f i)) (fun i => X (Sum.inr i))) (p j)) =
        eval₂ φ (Sum.elim (fun i => eval₂ φ x (f i)) y) (p j) := by
    intro y j
    rw [← coe_eval₂Hom, eval₂Hom_bind₁, coe_eval₂Hom]
    congr 1
    funext i
    rcases i with i | i <;> simp [eval₂_rename]
  simp only [Set.mem_ofPred_eq, hp, key]

/-- **Preimages of Diophantine sets under coordinate maps are Diophantine.** Let
$\varphi : A \to R$ be a ring homomorphism of commutative rings, let $T \subseteq R^k$ be
Diophantine over $R$ with coefficients from $A$ through $\varphi$, and let
$\sigma : \{0, \dots, k - 1\} \to \{0, \dots, k' - 1\}$ be any map. Then
$\{x \in R^{k'} \mid x \circ \sigma \in T\}$ is Diophantine over $R$ with coefficients from $A$
through $\varphi$. This covers permutations, duplications and omissions of coordinates. -/
theorem IsDiophantine.comp {φ : A →+* R} {k k' : ℕ} {T : Set (Fin k → R)}
    (hT : IsDiophantine φ T) (σ : Fin k → Fin k') :
    IsDiophantine φ {x : Fin k' → R | x ∘ σ ∈ T} := by
  simpa [Function.comp_def] using hT.preimage_eval₂ fun i => X (σ i)

/-- **Images of Diophantine sets under polynomial maps are Diophantine.** Let
$\varphi : A \to R$ be a ring homomorphism of commutative rings, let $T \subseteq R^m$ be
Diophantine over $R$ with coefficients from $A$ through $\varphi$, and let $f_1, \dots, f_k$ be
polynomials with coefficients in $A$ in $m$ variables. Then the image
$\{x \in R^k \mid \exists t \in T,\ x_i = f_i(t) \text{ for all } i\}$ of $T$ under
$t \mapsto (f_1(t), \dots, f_k(t))$ is Diophantine over $R$ with coefficients from $A$ through
$\varphi$.

The point $t$ becomes a block of auxiliary variables, joined by the equations
$x_i - f_i(t) = 0$. -/
theorem IsDiophantine.image_eval₂ {φ : A →+* R} {k m : ℕ} {T : Set (Fin m → R)}
    (hT : IsDiophantine φ T) (f : Fin k → MvPolynomial (Fin m) A) :
    IsDiophantine φ {x : Fin k → R | ∃ t ∈ T, ∀ i, x i = eval₂ φ t (f i)} := by
  obtain ⟨n, κ, _, p, hp⟩ := hT.exists_family
  refine isDiophantine_of_finite φ (ι := Fin m ⊕ Fin n)
    (Sum.elim (fun j => rename Sum.inr (p j))
      (fun i => X (Sum.inl i) - rename (Sum.inr ∘ Sum.inl) (f i))) fun x => ?_
  simp only [Set.mem_ofPred_eq, hp, Sum.forall, Sum.elim_inl, Sum.elim_inr, eval₂_rename,
    eval₂_sub, eval₂_X, Sum.elim_comp_inr, ← Function.comp_assoc, sub_eq_zero]
  constructor
  · rintro ⟨t, ⟨y, hy⟩, hx⟩
    exact ⟨Sum.elim t y, hy, hx⟩
  · rintro ⟨w, hy, hx⟩
    refine ⟨w ∘ Sum.inl, ⟨w ∘ Sum.inr, ?_⟩, hx⟩
    rwa [Sum.elim_comp_inl_inr]

/-- **Projections of Diophantine sets are Diophantine.** Let $\varphi : A \to R$ be a ring
homomorphism of commutative rings and let $S \subseteq R^{k + m}$ be Diophantine over $R$ with
coefficients from $A$ through $\varphi$. Then
$\{x \in R^k \mid \exists z \in R^m,\ (x, z) \in S\}$ is Diophantine over $R$ with coefficients
from $A$ through $\varphi$. Here $(x, z) \in R^{k + m}$ is `Fin.append x z`: the first $k$
coordinates are those of $x$, the last $m$ those of $z$. -/
theorem IsDiophantine.exists_proj {φ : A →+* R} {k m : ℕ} {S : Set (Fin (k + m) → R)}
    (hS : IsDiophantine φ S) :
    IsDiophantine φ {x : Fin k → R | ∃ z : Fin m → R, Fin.append x z ∈ S} := by
  convert hS.image_eval₂ (fun i : Fin k => X (Fin.castAdd m i)) using 1
  ext x
  simp only [Set.mem_ofPred_eq, eval₂_X]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨_, hz, fun i => (Fin.append_left x z i).symm⟩
  · rintro ⟨t, ht, hx⟩
    refine ⟨fun i => t (Fin.natAdd k i), ?_⟩
    have : x = fun i => t (Fin.castAdd m i) := funext hx
    rwa [this, Fin.append_castAdd_natAdd]

/-- In a formally real commutative ring, a finite sum of squares vanishes only if every term
does. -/
private theorem sum_sq_eq_zero_iff [IsFormallyReal R] {ι : Type*} (I : Finset ι) (a : ι → R) :
    ∑ i ∈ I, a i ^ 2 = 0 ↔ ∀ i ∈ I, a i = 0 := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert j I hj ih =>
    rw [Finset.sum_insert hj, Finset.forall_mem_insert, ← ih]
    have hj2 : IsSumSq (a j ^ 2) := by
      have := IsSumSq.sum_sq {j} a
      rwa [Finset.sum_singleton] at this
    constructor
    · intro h
      exact ⟨IsReduced.eq_zero _ ⟨2, IsFormallyReal.eq_zero_of_add_right hj2
          (IsSumSq.sum_sq I a) h⟩,
        IsFormallyReal.eq_zero_of_add_left hj2 (IsSumSq.sum_sq I a) h⟩
    · rintro ⟨h1, h2⟩
      simp [h1, h2]

/-- **One polynomial suffices over a formally real ring.** Let $\varphi : A \to R$ be a ring
homomorphism of commutative rings, where $R$ is formally real: a sum of squares in $R$ vanishes
only if each square does (for instance a linearly ordered ring such as $R = \mathbb{Q}$, with
$A = \mathbb{Z}$). A set $S \subseteq R^k$ is Diophantine over $R$ with
coefficients from $A$ through $\varphi$ if and only if there are $n \in \mathbb{N}$ and one
polynomial $p$ with coefficients in $A$ in the variables $x_1, \dots, x_k, y_1, \dots, y_n$ such
that $x \in S$ if and only if $p(x, y) = 0$ for some $y \in R^n$.

The single polynomial is the sum of the squares of the polynomials of a system.

Source: B. Poonen, "Hilbert's tenth problem over rings of number-theoretic interest" (2003),
Proposition 8.5 and its proof, p. 7: "Transform each conjunction of polynomial equations
$(p = 0) \wedge (q = 0)$ to $f(p, q) = 0$", here with $f(x, y) = x^2 + y^2$; see also
Example 6.3, p. 4, where three equations are combined into
"$(a - bc)^2 + (bp + 2q - 1)^2 + (cr + 3s - 1)^2 = 0$". -/
theorem IsDiophantine.iff_single [IsFormallyReal R] (φ : A →+* R) {k : ℕ}
    (S : Set (Fin k → R)) :
    IsDiophantine φ S ↔ ∃ (n : ℕ) (p : MvPolynomial (Fin k ⊕ Fin n) A),
      ∀ x : Fin k → R, x ∈ S ↔ ∃ y : Fin n → R, eval₂ φ (Sum.elim x y) p = 0 := by
  classical
  constructor
  · rintro ⟨n, P, hP⟩
    refine ⟨n, ∑ q ∈ P, q ^ 2, fun x => ?_⟩
    simp only [hP, eval₂_sum, eval₂_pow, sum_sq_eq_zero_iff]
  · rintro ⟨n, p, hp⟩
    exact ⟨n, {p}, fun x => by simp [hp]⟩

/-- **Nonzeroness of a coordinate is Diophantine over a field.** Let $\varphi : A \to K$ be a ring
homomorphism from a commutative ring to a field and let $i \in \{0, \dots, k - 1\}$. The set
$\{x \in K^k \mid x_i \neq 0\}$ is Diophantine over $K$ with coefficients from $A$ through
$\varphi$: $x_i \neq 0$ if and only if $x_i y = 1$ for some $y \in K$. -/
theorem isDiophantine_setOf_ne_zero {K : Type*} [Field K] (φ : A →+* K) {k : ℕ} (i : Fin k) :
    IsDiophantine φ {x : Fin k → K | x i ≠ 0} := by
  refine isDiophantine_of_finite φ (ι := Unit) (κ := Unit)
    (fun _ => X (Sum.inl i) * X (Sum.inr ()) - 1) fun x => ?_
  simp only [Set.mem_ofPred_eq, eval₂_sub, eval₂_mul, eval₂_X, eval₂_one, Sum.elim_inl,
    Sum.elim_inr, sub_eq_zero, forall_const]
  constructor
  · intro hx
    exact ⟨fun _ => (x i)⁻¹, mul_inv_cancel₀ hx⟩
  · rintro ⟨y, hy⟩ hx
    simp [hx] at hy

end MetaMathlibExt
