/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.GroupTheory.Nilpotent
import Mathlib.Logic.Equiv.Nat
import Mathlib.SetTheory.Cardinal.Basic

/-!
# Width of the lattice of closed subgroup functors (Kourovka Notebook Problem 16.82)

Kourovka Notebook, Archive of Solved Problems, Problem 16.82 (A. N. Skiba): let `𝔛` be a non-empty
class of finite groups closed under homomorphic images, subgroups and direct products, and let
`F(𝔛)` be the lattice of closed subgroup functors on `𝔛`. Is there a non-nilpotent class `𝔛` such
that the width of `F(𝔛)` is at most `|π(𝔛)|`, where `π(𝔛)` is the set of prime divisors of the
orders of the groups in `𝔛`?

The theorem `existsNonnilpotentClassOfSmallWidth_refuted` gives a negative answer.

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The Kourovka
Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.82 (A. N.
Skiba). UnsolvedMath record UM-00701273 (`KOU-16.82`), dataset ulamai/UnsolvedMath v1.8.0.

Classes of finite groups are predicates on finite groups in `Type`. A subgroup functor assigns a set
of subgroups to every finite group, only the values on `𝔛` mattering, with the problem's conditions:
`G ∈ τ(G)`, closure under images and preimages along epimorphisms between groups of `𝔛`, and, for
closed functors, `τ(H) ⊆ τ(G)` for `H ∈ τ(G)`. The order of `F(𝔛)` compares values on `𝔛`, so
functors agreeing on `𝔛` are comparable and never lie in a common antichain. Width at most `|π(𝔛)|`
means that every antichain has at most `|π(𝔛)|` elements (as cardinals). Non-nilpotent means
containing a non-nilpotent group.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted

/-- **Classes of finite groups (Kourovka 16.82 setting).** A class $\mathfrak{X}$ of finite groups
is a predicate on finite groups $G$ (with carrier in the lowest type universe, together with their
group structure); the groups satisfying it are the members of the class, written
$G \in \mathfrak{X}$. -/
abbrev FiniteGroupClass : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Prop

/-- **Closed classes of finite groups.** A class $\mathfrak{X}$ of finite groups is closed when it
contains at least one group and is closed under homomorphic images, subgroups and direct products:
if $G \in \mathfrak{X}$ and $f : G \to H$ is a surjective homomorphism onto a finite group $H$,
then $H \in \mathfrak{X}$; every subgroup of a group in $\mathfrak{X}$ lies in $\mathfrak{X}$; and
if $G, H \in \mathfrak{X}$, then $G \times H \in \mathfrak{X}$. -/
def IsClosedClass (X : FiniteGroupClass) : Prop :=
  (∃ (G : Type) (_ : Group G) (_ : Finite G), X G) ∧
    (∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H] (f : G →* H),
      Function.Surjective f → X G → X H) ∧
    (∀ (G : Type) [Group G] [Finite G] (H : Subgroup G), X G → X H) ∧
    ∀ (G H : Type) [Group G] [Finite G] [Group H] [Finite H], X G → X H → X (G × H)

/-- **Subgroup assignments.** A subgroup assignment $\tau$ assigns to every finite group $G$ (with
carrier in the lowest type universe) a set $\tau(G)$ of subgroups of $G$. -/
abbrev SubgroupAssignment : Type 1 :=
  ∀ (G : Type) [Group G] [Finite G], Set (Subgroup G)

/-- **Closed subgroup functors.** Let $\mathfrak{X}$ be a class of finite groups. A subgroup
assignment $\tau$ is a closed subgroup functor on $\mathfrak{X}$ (A. N. Skiba) when the following
three conditions hold. For every $G \in \mathfrak{X}$, $G \in \tau(G)$. For every surjective
homomorphism $\varphi : A \to B$ with $A, B \in \mathfrak{X}$, $\varphi(H) \in \tau(B)$ for every
$H \in \tau(A)$ and $\varphi^{-1}(T) \in \tau(A)$ for every $T \in \tau(B)$. For every
$G \in \mathfrak{X}$, every $H \in \tau(G)$ and every $K \in \tau(H)$, the subgroup $K$, viewed as
a subgroup of $G$, lies in $\tau(G)$; that is, $\tau(H) \subseteq \tau(G)$. -/
def IsClosedSubgroupFunctor (X : FiniteGroupClass) (τ : SubgroupAssignment) : Prop :=
  (∀ (G : Type) [Group G] [Finite G], X G → ⊤ ∈ τ G) ∧
    (∀ (A B : Type) [Group A] [Finite A] [Group B] [Finite B] (φ : A →* B),
      Function.Surjective φ → X A → X B →
        (∀ H ∈ τ A, H.map φ ∈ τ B) ∧ ∀ T ∈ τ B, T.comap φ ∈ τ A) ∧
    ∀ (G : Type) [Group G] [Finite G], X G → ∀ H ∈ τ G, ∀ K ∈ τ H, K.map H.subtype ∈ τ G

/-- **Order on subgroup functors.** Let $\mathfrak{X}$ be a class of finite groups. For subgroup
assignments $\tau_1$ and $\tau_2$, $\tau_1 \le \tau_2$ on $\mathfrak{X}$ when
$\tau_1(G) \subseteq \tau_2(G)$ for every $G \in \mathfrak{X}$. This is the order of the lattice
$F(\mathfrak{X})$ of closed subgroup functors on $\mathfrak{X}$. -/
def FunctorLE (X : FiniteGroupClass) (τ₁ τ₂ : SubgroupAssignment) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], X G → τ₁ G ⊆ τ₂ G

/-- **Prime divisors of a class of finite groups.** For a class $\mathfrak{X}$ of finite groups,
$\pi(\mathfrak{X})$ is the set of primes $p$ that divide the order of some group in
$\mathfrak{X}$. -/
def primesOf (X : FiniteGroupClass) : Set ℕ :=
  {p | p.Prime ∧ ∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ p ∣ Nat.card G}

/-- **Kourovka Problem 16.82 (Skiba).** For a class $\mathfrak{X}$ of finite groups, let
$\pi(\mathfrak{X})$ be the set of primes dividing the order of some group in $\mathfrak{X}$, and
for subgroup assignments $\tau_1, \tau_2$ write $\tau_1 \le \tau_2$ on $\mathfrak{X}$ when
$\tau_1(G) \subseteq \tau_2(G)$ for every $G \in \mathfrak{X}$. There is a class $\mathfrak{X}$ of
finite groups that contains at least one group, is closed under homomorphic images, subgroups and
direct products, and contains a non-nilpotent group, such that the lattice $F(\mathfrak{X})$ of
closed subgroup functors on $\mathfrak{X}$ has width at most $|\pi(\mathfrak{X})|$: every set of
closed subgroup functors on $\mathfrak{X}$ in which no two distinct members $\tau_1, \tau_2$
satisfy $\tau_1 \le \tau_2$ on $\mathfrak{X}$ has cardinality at most $|\pi(\mathfrak{X})|$. -/
def existsNonnilpotentClassOfSmallWidth : Prop :=
  ∃ X : FiniteGroupClass, IsClosedClass X ∧
    (∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ ¬ Group.IsNilpotent G) ∧
    ∀ A : Set SubgroupAssignment, (∀ τ ∈ A, IsClosedSubgroupFunctor X τ) →
      (∀ τ₁ ∈ A, ∀ τ₂ ∈ A, τ₁ ≠ τ₂ → ¬ FunctorLE X τ₁ τ₂) →
      Cardinal.mk A ≤ Cardinal.lift.{1} (Cardinal.mk (primesOf X))

-- A normal maximal step is distinguished by its index. All nonnormal maximal steps
-- receive the extra label `none`.
private noncomputable def label {G : Type} [Group G] (M : Subgroup G) : Option ℕ :=
  open Classical in if M.Normal then some M.index else none

private theorem label_comap {G Q : Type} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) (M : Subgroup Q) : label (M.comap f) = label M := by
  classical
  simp only [label, Subgroup.normal_comap_iff_of_surjective hf, M.index_comap_of_surjective hf]

-- Descend from the whole group by maximal inclusions whose labels belong to S.
private inductive Chain (S : Set (Option ℕ)) (G : Type) [Group G] : Subgroup G → Prop
  | top : Chain S G ⊤
  | step {K : Subgroup G} (prev : Chain S G K) (M : Subgroup K)
      (maximal : IsCoatom M) (allowed : label M ∈ S) : Chain S G (M.map K.subtype)

private theorem maximal_map {G Q : Type} [Group G] [Group Q] (f : G →* Q)
    (hf : Function.Surjective f) {M : Subgroup G} (hm : IsCoatom M) (h : M.map f ≠ ⊤) :
    IsCoatom (M.map f) ∧ label (M.map f) = label M := by
  have heq : (M.map f).comap f = M := by
    symm
    apply (eq_or_lt_of_le (Subgroup.le_comap_map f M)).resolve_right
    intro hlt
    have htop := hm.2 _ hlt
    exact h ((Subgroup.comap_injective hf) (htop.trans (Subgroup.comap_top f).symm))
  refine ⟨⟨h, fun L hL ↦ ?_⟩, ?_⟩
  · apply Subgroup.comap_injective hf
    rw [Subgroup.comap_top]
    apply hm.2
    rwa [← heq, Subgroup.comap_lt_comap_of_surjective hf]
  · rw [← label_comap f hf, heq]

private theorem chain_map {G Q : Type} [Group G] [Group Q] {S : Set (Option ℕ)}
    {H : Subgroup G} (h : Chain S G H) (f : G →* Q) (ht : Chain S Q f.range) :
    Chain S Q (H.map f) := by
  induction h with
  | top => simpa only [Subgroup.map_top] using ht
  | @step K prev M hm hs ih =>
    let g := f.subgroupMap K
    have heq : (M.map K.subtype).map f = (M.map g).map (K.map f).subtype := by
      rw [Subgroup.map_map, Subgroup.map_map]
      rfl
    rw [heq]
    by_cases he : M.map g = ⊤
    · simpa only [he, Subgroup.map_top, Subgroup.range_subtype] using ih
    · have ⟨hm', hl⟩ := maximal_map g (f.subgroupMap_surjective K) hm he
      exact .step ih _ hm' (hl ▸ hs)

private theorem chain_comap {G Q : Type} [Group G] [Group Q] {S : Set (Option ℕ)}
    {H : Subgroup Q} (h : Chain S Q H) (f : G →* Q) (hf : Function.Surjective f) :
    Chain S G (H.comap f) := by
  induction h with
  | top => simpa using (Chain.top : Chain S G ⊤)
  | @step K prev M hm hs ih =>
    let g := f.subgroupComap K
    have hg : Function.Surjective g := f.subgroupComap_surjective K hf
    have heq : (M.map K.subtype).comap f = (M.comap g).map (K.comap f).subtype := by
      ext x
      constructor
      · rintro ⟨y, hy, he⟩
        have hx : f x ∈ K := he ▸ y.property
        have hxy : g ⟨x, hx⟩ = y := Subtype.ext he.symm
        exact ⟨⟨x, hx⟩, (show g ⟨x, hx⟩ ∈ M from hxy ▸ hy), rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨g y, hy, rfl⟩
    rw [heq]
    exact .step ih _ (Subgroup.isCoatom_comap_of_surjective hg hm) (label_comap g hg M ▸ hs)

private def assignment (S : Set (Option ℕ)) : SubgroupAssignment := fun G _ _ ↦ {H | Chain S G H}

private theorem assignment_closed (X : FiniteGroupClass) (S : Set (Option ℕ)) :
    IsClosedSubgroupFunctor X (assignment S) := by
  refine ⟨fun _ _ _ _ ↦ .top, ?_, ?_⟩
  · intro A B _ _ _ _ f hf _ _
    have ht : Chain S B f.range := (MonoidHom.range_eq_top.mpr hf) ▸ Chain.top
    exact ⟨fun _ h ↦ chain_map h f ht, fun _ h ↦ chain_comap h f hf⟩
  · intro G _ _ _ H hH K hK
    change Chain S G H at hH
    exact chain_map hK H.subtype (by simpa only [Subgroup.range_subtype] using hH)

-- At a maximal subgroup a descending chain can have only one step.
private theorem maximal_mem {G : Type} [Group G] [Finite G] (M : Subgroup G)
    (hm : IsCoatom M) (S : Set (Option ℕ)) : M ∈ assignment S G ↔ label M ∈ S := by
  have ht : Function.Surjective (⊤ : Subgroup G).subtype := fun x ↦ ⟨⟨x, trivial⟩, rfl⟩
  constructor
  · intro h
    change Chain S G M at h
    cases h with
    | top => exact (hm.1 rfl).elim
    | @step K prev L hL hs =>
      have hlt : L.map K.subtype < K := by
        simpa only [Subgroup.map_top, Subgroup.range_subtype] using
          (Subgroup.map_subtype_lt_map_subtype (G' := K)).2 (lt_top_iff_ne_top.2 hL.1)
      obtain rfl : K = ⊤ := hm.2 _ hlt
      exact (maximal_map _ ht hL hm.1).2 ▸ hs
  · intro hs
    have h := Chain.step (Chain.top (G := G) (S := S)) (M.comap (⊤ : Subgroup G).subtype)
      (Subgroup.isCoatom_comap_of_surjective ht hm) (label_comap _ ht M ▸ hs)
    change Chain S G M
    simpa only [Subgroup.map_comap_eq_self_of_surjective ht] using h

private def primeLabel {X : FiniteGroupClass} : Option (primesOf X) → Option ℕ :=
  Option.map Subtype.val

private theorem exists_maximal_label {X : FiniteGroupClass} (hX : IsClosedClass X)
    (hn : ∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ ¬ Group.IsNilpotent G)
    (i : Option (primesOf X)) :
    ∃ (G : Type) (_ : Group G) (_ : Finite G) (M : Subgroup G),
      X G ∧ IsCoatom M ∧ label M = primeLabel i := by
  classical
  cases i with
  | none =>
    obtain ⟨G, _, _, hx, hn⟩ := hn
    have hh := (Group.isNilpotent_of_finite_tfae (G := G)).out 1 3
    have hn' : ¬ ∀ M : Subgroup G, IsCoatom M → M.Normal := hn ∘ hh.mpr
    push Not at hn'
    obtain ⟨M, hm, hM⟩ := hn'
    exact ⟨G, inferInstance, inferInstance, M, hx, hm, by simp [label, hM, primeLabel]⟩
  | some p =>
    obtain ⟨hp, G, _, _, hx, hd⟩ := p.property
    let : Fact p.val.Prime := ⟨hp⟩
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p.val hd
    let P := Subgroup.zpowers g
    have hi : (⊥ : Subgroup P).index = p.val := by
      rw [Subgroup.index_bot, Nat.card_zpowers, hg]
    exact ⟨P, inferInstance, inferInstance, ⊥, hX.2.2.1 G P hx,
      Subgroup.isCoatom_of_index_prime (hi ▸ hp), by simp [label, hi, primeLabel]⟩

private theorem exists_antichain {X : FiniteGroupClass} (hX : IsClosedClass X)
    (hn : ∃ (G : Type) (_ : Group G) (_ : Finite G), X G ∧ ¬ Group.IsNilpotent G)
    {ι : Type} (s : ι → Set (Option (primesOf X))) (hs : ∀ i j, s i ⊆ s j → i = j) :
    ∃ A : Set SubgroupAssignment, (∀ τ ∈ A, IsClosedSubgroupFunctor X τ) ∧
      (∀ τ₁ ∈ A, ∀ τ₂ ∈ A, τ₁ ≠ τ₂ → ¬ FunctorLE X τ₁ τ₂) ∧
      Cardinal.mk A = Cardinal.lift.{1} (Cardinal.mk ι) := by
  let F (i : ι) : SubgroupAssignment := assignment (primeLabel '' s i)
  have hinj : Function.Injective (primeLabel (X := X)) :=
    Option.map_injective Subtype.val_injective
  have reflects {i j : ι} (h : FunctorLE X (F i) (F j)) : i = j := by
    apply hs
    intro t ht
    obtain ⟨G, _, _, M, hx, hm, hl⟩ := exists_maximal_label hX hn t
    have hmem : M ∈ F i G := (maximal_mem M hm _).2 (hl ▸ Set.mem_image_of_mem _ ht)
    obtain ⟨u, hu, he⟩ := (maximal_mem M hm _).1 (h G hx hmem)
    exact hinj (he.trans hl) ▸ hu
  have hF : Function.Injective F := by
    intro i j he
    apply reflects
    rw [he]
    exact fun _ _ _ _ ↦ Set.Subset.rfl
  refine ⟨Set.range F, ?_, ?_, ?_⟩
  · rintro _ ⟨i, rfl⟩
    exact assignment_closed X _
  · rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩ hne hle
    exact hne (congrArg F (reflects hle))
  · simpa using Cardinal.mk_range_eq_of_injective hF

/-- **Kourovka Problem 16.82 has a negative answer.** For a class $\mathfrak{X}$ of finite groups,
let $\pi(\mathfrak{X})$ be the set of primes dividing the order of some group in $\mathfrak{X}$,
and for subgroup assignments $\tau_1, \tau_2$ write $\tau_1 \le \tau_2$ on $\mathfrak{X}$ when
$\tau_1(G) \subseteq \tau_2(G)$ for every $G \in \mathfrak{X}$. There is no class $\mathfrak{X}$ of
finite groups that contains at least one group, is closed under homomorphic images, subgroups and
direct products, contains a non-nilpotent group, and has the following property: every set of
closed subgroup functors on $\mathfrak{X}$ in which no two distinct members $\tau_1, \tau_2$
satisfy $\tau_1 \le \tau_2$ on $\mathfrak{X}$ has cardinality at most $|\pi(\mathfrak{X})|$. In
other words, for every such class the lattice $F(\mathfrak{X})$ of closed subgroup functors on
$\mathfrak{X}$ has width greater than $|\pi(\mathfrak{X})|$.

The Kourovka Archive answers 16.82 "No such classes exist", citing Kamornikov (2010).

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group Theory: The
Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Archive of Solved Problems, Problem 16.82
(A. N. Skiba); resolution: S. F. Kamornikov, Siberian Math. J. 51 (2010), no. 5, 824-829, Kourovka
Archive, Problem 16.82 (No such classes exist).
-/
theorem existsNonnilpotentClassOfSmallWidth_refuted :
    ¬ existsNonnilpotentClassOfSmallWidth := by
  classical
  rintro ⟨X, hX, hn, hwidth⟩
  have bound {ι : Type} (s : ι → Set (Option (primesOf X))) (hs : ∀ i j, s i ⊆ s j → i = j) :
      Cardinal.mk ι ≤ Cardinal.mk (primesOf X) := by
    obtain ⟨A, hclosed, hanti, hcard⟩ := exists_antichain hX hn s hs
    simpa only [hcard, Cardinal.lift_le] using hwidth A hclosed hanti
  rcases (primesOf X).finite_or_infinite with hfin | hinf
  · -- One singleton for each prime, plus the singleton for nonnormal maximal subgroups.
    let _ := hfin.fintype
    have h := bound (fun i ↦ {i}) (by simp)
    simp [Cardinal.mk_fintype] at h
  · -- Pair distinct primes and choose one prime from each pair for every binary sequence.
    let e := Equiv.boolProdNatEquivNat.toEmbedding.trans (hinf.natEmbedding _)
    let s (b : ℕ → Bool) : Set (Option (primesOf X)) := Set.range fun n ↦ some (e (b n, n))
    have h := bound s (by
      intro b c hbc
      funext n
      obtain ⟨m, hm⟩ := hbc (show some (e (b n, n)) ∈ s b from ⟨n, rfl⟩)
      obtain ⟨h, rfl⟩ := Prod.mk.inj (e.injective (Option.some.inj hm))
      exact h.symm)
    have hlarge : Cardinal.mk ℕ < Cardinal.mk (ℕ → Bool) := by
      simpa only [Cardinal.mk_arrow, Cardinal.lift_id, Cardinal.mk_bool] using
        Cardinal.cantor (Cardinal.mk ℕ)
    exact hlarge.not_ge (h.trans (Cardinal.mk_set_le _))

end MathlibExt.GroupTheory.ClosedSubgroupFunctorLatticeWidthKourovka16Problem82Wanted
