/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Post correspondence problem is undecidable over a binary alphabet
-/
module

public import CSLibExt.Computability.Decidability.PCPUndecidable

/-!
# The Post correspondence problem is undecidable over a binary alphabet

An injective word homomorphism preserves and reflects PCP solutions (`pcp_map_iff`): the image
of a solution is a solution, and a solution of the image instance comes from a sequence of
original dominoes whose tops and bottoms have equal images, hence are equal.

Over a finite alphabet the unary code `a ↦ 1ⁱ 0` (`i` the index of `a`) is such a homomorphism to
`Bool` (`unaryHom_injective`), so PCP over a finite alphabet many-one reduces to PCP over `Bool`
(`manyOneReducible_pcp_bool`), and PCP over `Bool` is undecidable (`not_tm2Decidable_pcp_bool`).

## Main results

- `pcp_map_iff`, `unaryHom_injective`, `manyOneReducible_pcp_bool`, `not_tm2Decidable_pcp_bool`.

## References

* M. Sipser, *Introduction to the Theory of Computation*, 3rd ed., Cengage, 2013, §5.2.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Decidability.Post

variable {α β : Type*}

/-- **Image of a PCP instance under a word map.** Given a map $f$ from words over $\alpha$
to words over $\beta$ and a list $P$ of dominoes over $\alpha$, the image of $P$ under $f$ is the
list of dominoes over $\beta$ obtained by replacing each domino $(u, v)$ of $P$ by $(f(u), f(v))$,
in the same order. -/
def mapInstance (f : List α → List β) (P : List (Domino α)) : List (Domino β) :=
  P.map fun d ↦ (f d.1, f d.2)

theorem top_map_flatMap (h : α → List β) (s : List (Domino α)) :
    top (mapInstance (fun w ↦ w.flatMap h) s) = (top s).flatMap h := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    rw [show mapInstance (fun w ↦ w.flatMap h) (d :: s) =
      (d.1.flatMap h, d.2.flatMap h) :: mapInstance (fun w ↦ w.flatMap h) s from rfl,
      top_cons, ih, top_cons, List.flatMap_append]

theorem bottom_map_flatMap (h : α → List β) (s : List (Domino α)) :
    bottom (mapInstance (fun w ↦ w.flatMap h) s) = (bottom s).flatMap h := by
  induction s with
  | nil => rfl
  | cons d s ih =>
    rw [show mapInstance (fun w ↦ w.flatMap h) (d :: s) =
      (d.1.flatMap h, d.2.flatMap h) :: mapInstance (fun w ↦ w.flatMap h) s from rfl,
      bottom_cons, ih, bottom_cons, List.flatMap_append]

/-- **An injective word homomorphism preserves and reflects PCP solvability.** Let $h$ map each
letter of $\alpha$ to a word over $\beta$, and extend it to words by
$h(a_1 \cdots a_n) = h(a_1) \cdots h(a_n)$. If this extension is injective on words over $\alpha$,
then for every list $P$ of dominoes over $\alpha$, the list obtained from $P$ by replacing each
domino $(u, v)$ by $(h(u), h(v))$ has a PCP solution if and only if $P$ has a PCP solution. -/
theorem pcp_map_iff {h : α → List β} (hinj : Function.Injective fun w : List α ↦ w.flatMap h)
    (P : List (Domino α)) : PCP (mapInstance (fun w ↦ w.flatMap h) P) ↔ PCP P := by
  constructor
  · rintro ⟨s', hne, hmem, htop⟩
    -- pull the solution back along the map
    have hpre : ∀ s' : List (Domino β), (∀ d ∈ s', d ∈ mapInstance (fun w ↦ w.flatMap h) P) →
        ∃ s : List (Domino α), (∀ d ∈ s, d ∈ P) ∧ mapInstance (fun w ↦ w.flatMap h) s = s' := by
      intro s'
      induction s' with
      | nil => exact fun _ ↦ ⟨[], by simp, rfl⟩
      | cons d s' ih =>
        intro hd
        obtain ⟨s, hs, rfl⟩ := ih fun e he ↦ hd e (List.mem_cons_of_mem _ he)
        obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp (hd d List.mem_cons_self)
        refine ⟨d₀ :: s, fun e he ↦ ?_, rfl⟩
        rcases List.mem_cons.mp he with rfl | he
        · exact hd₀
        · exact hs e he
    obtain ⟨s, hs, rfl⟩ := hpre s' hmem
    refine ⟨s, fun h' ↦ hne (by simp [h', mapInstance]), hs, hinj ?_⟩
    simpa [top_map_flatMap, bottom_map_flatMap] using htop
  · rintro ⟨s, hne, hmem, htop⟩
    refine ⟨mapInstance (fun w ↦ w.flatMap h) s, by simpa [mapInstance] using hne,
      fun d hd ↦ ?_, by rw [top_map_flatMap, bottom_map_flatMap, htop]⟩
    obtain ⟨d₀, hd₀, rfl⟩ := List.mem_map.mp hd
    exact List.mem_map.mpr ⟨d₀, hmem d₀ hd₀, rfl⟩

/-! ### The unary code -/

/-- **Unary code of a letter.** Given an indexing $e$ assigning a natural number to each letter of
$\alpha$, the unary code of a letter $a$ is the Boolean word consisting of $e(a)$ copies of
$\mathrm{true}$ followed by one $\mathrm{false}$; writing $1$ for true and $0$ for false, it is
$1^{e(a)} 0$. -/
def unaryCode (e : α → ℕ) (a : α) : List Bool := List.replicate (e a) true ++ [false]

theorem eq_of_replicate_true_append {i j : ℕ} {u v : List Bool}
    (h : List.replicate i true ++ false :: u = List.replicate j true ++ false :: v) :
    i = j ∧ u = v := by
  induction i generalizing j with
  | zero =>
    cases j with
    | zero => simpa using h
    | succ j => simp [List.replicate_succ] at h
  | succ i ih =>
    cases j with
    | zero => simp [List.replicate_succ] at h
    | succ j =>
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨rfl, rfl⟩ := ih h
      exact ⟨rfl, rfl⟩

/-- **The unary code of an injective indexing is uniquely decodable.** Let $e$ be an injective map
from $\alpha$ to the natural numbers, and let $c(a)$ be the unary code of a letter $a$: $e(a)$
copies of $\mathrm{true}$ followed by one $\mathrm{false}$. Then the map sending a word
$a_1 \cdots a_n$ over $\alpha$ to the Boolean word $c(a_1) \cdots c(a_n)$ is injective. -/
theorem unaryHom_injective {e : α → ℕ} (he : Function.Injective e) :
    Function.Injective fun w : List α ↦ w.flatMap (unaryCode e) := by
  intro w
  induction w with
  | nil =>
    intro v h
    cases v with
    | nil => rfl
    | cons b v => simp [unaryCode] at h
  | cons a w ih =>
    intro v h
    cases v with
    | nil => simp [unaryCode] at h
    | cons b v =>
      simp only [List.flatMap_cons, unaryCode, List.append_assoc, List.singleton_append] at h
      obtain ⟨hab, hwv⟩ := eq_of_replicate_true_append h
      rw [he hab, ih hwv]

/-! ### Undecidability over `Bool` -/

/-- **PCP over a finite alphabet many-one reduces to PCP over the binary alphabet.** Let $\alpha$
be a finite alphabet with a primitive recursive encoding of its letters as natural numbers. Then
the Post correspondence problem over $\alpha$ is many-one reducible to the Post correspondence
problem over the two-letter alphabet of Booleans $\mathrm{true}$ and $\mathrm{false}$: there is a
computable map $f$ sending each finite list $P$ of dominoes over $\alpha$ to a finite list $f(P)$
of dominoes over the Booleans such that $P$ has a PCP solution if and only if $f(P)$ has a PCP
solution. -/
theorem manyOneReducible_pcp_bool [Finite α] [Primcodable α] :
    ManyOneReducible (PCP (α := α)) (PCP (α := Bool)) := by
  classical
  have := Fintype.ofFinite α
  let e : α → ℕ := fun a ↦ (Fintype.equivFin α a : ℕ)
  have he : Function.Injective e := fun a b hab ↦
    (Fintype.equivFin α).injective (Fin.ext hab)
  have hcode : Primrec (unaryCode e) := Primrec.dom_finite _
  have hword : Primrec fun w : List α ↦ w.flatMap (unaryCode e) :=
    Primrec.list_flatMap Primrec.id (hcode.comp Primrec.snd).to₂
  refine ⟨mapInstance fun w ↦ w.flatMap (unaryCode e),
    (Primrec.list_map Primrec.id (Primrec.pair (hword.comp (Primrec.fst.comp Primrec.snd))
      (hword.comp (Primrec.snd.comp Primrec.snd))).to₂).to_comp,
    fun P ↦ (pcp_map_iff (unaryHom_injective he) P).symm⟩

end Cslib.Decidability.Post

namespace Cslib.Decidability

open Post

/-- **The Post correspondence problem is undecidable over the binary alphabet.** The Post
correspondence problem over the two-letter alphabet of Booleans $\mathrm{true}$ and
$\mathrm{false}$, that is, the property of a finite list $P$ of dominoes over the Booleans of
having a PCP solution, is not decidable by a multi-stack Turing machine: no multi-stack machine
computes a total function $g : \mathbb{N} \to \mathbb{N}$ such that, for every such $P$ with
natural-number encoding $n_P$, $g(n_P) = 1$ exactly when $P$ has a PCP solution. -/
theorem not_tm2Decidable_pcp_bool : ¬TM2Decidable (PCP (α := Bool)) := by
  obtain ⟨α, _, _, h⟩ := exists_not_tm2Decidable_pcp
  exact fun hd ↦ h (tm2Decidable_of_manyOneReducible manyOneReducible_pcp_bool hd)

end Cslib.Decidability
