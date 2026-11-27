/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Closure properties of computable and r.e. predicates
-/
module

public import Mathlib.Computability.PartrecCode
public import Mathlib.Computability.RE

/-!
# Closure properties of computable and r.e. predicates

Mathlib's `ComputablePred` is closed under negation (`ComputablePred.not`). This file adds
closure of `ComputablePred` under `∧` and `∨`, of `REPred` under `∧` and `∨` (the latter by
running both in parallel with `Partrec.merge'`), and of `REPred` under existential and
universal quantification over a primitive recursive finite list of candidates, by
dovetailing with the step-bounded evaluator `Nat.Partrec.Code.evaln`. Dovetailing over all
candidates also selects a witness of an r.e. relation partial recursively
(`REPred.exists_partrec_choose`), whose domain is the unbounded existential projection. It also
shows that `List.any` with a computable test is computable.

## Main results

- `ComputablePred.and`, `ComputablePred.or`, `REPred.and`, `REPred.or`.
- `REPred.exists_mem`, `REPred.forall_mem`, and the unbounded `REPred.exists`.
- `REPred.exists_partrec_choose`: selection of witnesses for r.e. relations.
- `computable_list_any`.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt


variable {α : Type*} [Primcodable α]

/-- **Computable predicates are closed under conjunction.** Let $\alpha$ be a type with a
primitive recursive encoding into $\mathbb{N}$. If $p$ and $q$ are computable predicates on
$\alpha$, then the predicate $a \mapsto p(a) \land q(a)$ is computable. -/
theorem ComputablePred.and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a ↦ p a ∧ q a := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp hp
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hq
  refine ComputablePred.computable_iff.mpr ⟨fun a ↦ f a && g a, ?_, ?_⟩
  · exact (Primrec.and.to_comp).comp hf hg
  · funext a
    simp

/-- **Computable predicates are closed under disjunction.** Let $\alpha$ be a type with a
primitive recursive encoding into $\mathbb{N}$. If $p$ and $q$ are computable predicates on
$\alpha$, then the predicate $a \mapsto p(a) \lor q(a)$ is computable. -/
theorem ComputablePred.or {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a ↦ p a ∨ q a := by
  obtain ⟨f, hf, rfl⟩ := ComputablePred.computable_iff.mp hp
  obtain ⟨g, hg, rfl⟩ := ComputablePred.computable_iff.mp hq
  refine ComputablePred.computable_iff.mpr ⟨fun a ↦ f a || g a, ?_, ?_⟩
  · exact (Primrec.or.to_comp).comp hf hg
  · funext a
    simp

/-- **Recursively enumerable predicates are closed under conjunction.** Let $\alpha$ be a type
with a primitive recursive encoding into $\mathbb{N}$. If $p$ and $q$ are recursively enumerable
predicates on $\alpha$, then the predicate $a \mapsto p(a) \land q(a)$ is recursively enumerable.

The proof runs one semi-decision procedure, then the other. -/
theorem REPred.and {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun a ↦ p a ∧ q a := by
  have hb : Partrec fun a ↦ (Part.assert (p a) fun _ ↦ Part.some ()).bind fun _ ↦
      Part.assert (q a) fun _ ↦ Part.some () :=
    Partrec.bind hp (hq.comp Computable.fst)
  refine hb.dom_re.of_eq fun a ↦ ⟨?_, ?_⟩
  · rintro ⟨⟨h₁, -⟩, h₂, -⟩
    exact ⟨h₁, h₂⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨⟨h₁, trivial⟩, h₂, trivial⟩

/-- **Recursively enumerable predicates are closed under disjunction.** Let $\alpha$ be a type
with a primitive recursive encoding into $\mathbb{N}$. If $p$ and $q$ are recursively enumerable
predicates on $\alpha$, then the predicate $a \mapsto p(a) \lor q(a)$ is recursively enumerable.

The proof runs both semi-decision procedures in parallel. -/
theorem REPred.or {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun a ↦ p a ∨ q a := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  refine hk.dom_re.of_eq fun a ↦ ?_
  rw [(H a).2]
  exact ⟨fun h ↦ h.imp (fun ⟨h, _⟩ ↦ h) (fun ⟨h, _⟩ ↦ h),
    fun h ↦ h.imp (fun h ↦ ⟨h, trivial⟩) (fun h ↦ ⟨h, trivial⟩)⟩

/-- **Bounded existential quantification preserves recursive enumerability.** Let $\alpha$ and
$\beta$ be types with primitive recursive encodings into $\mathbb{N}$, let $R$ be a relation
between $\alpha$ and $\beta$ that is recursively enumerable as a predicate on pairs $(a, b)$, and
let $c$ be a primitive recursive function sending each $a \in \alpha$ to a finite list $c(a)$ of
elements of $\beta$. Then the predicate $a \mapsto \exists b \in c(a),\ R(a, b)$ is recursively
enumerable.

The proof is by dovetailing: it searches for a step bound $k$ at which the simulation of the
semi-decision procedure for $R$ halts on $(a, b)$ for some $b$ in $c(a)$. -/
theorem REPred.exists_mem {β : Type*} [Primcodable β] {R : α → β → Prop}
    (hR : REPred fun p : α × β ↦ R p.1 p.2) {c : α → List β} (hc : Primrec c) :
    REPred fun a ↦ ∃ b ∈ c a, R a b := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.1 hR
  have hdom : ∀ a b, (Nat.Partrec.Code.eval code (Encodable.encode (a, b))).Dom ↔ R a b := by
    intro a b
    rw [hcode]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom]
    exact ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, trivial⟩⟩
  let D : α → ℕ → Bool := fun a k ↦ (c a).any fun b ↦
    (Nat.Partrec.Code.evaln k code (Encodable.encode (a, b))).isSome
  have hD : Primrec₂ D := by
    have hg : Primrec fun q : (α × ℕ) × β ↦
        (Nat.Partrec.Code.evaln q.1.2 code (Encodable.encode (q.1.1, q.2))).isSome :=
      Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const code))
        (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))))
    refine (Primrec.list_foldr (hc.comp Primrec.fst) (Primrec.const false)
      (Primrec.or.comp (hg.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun q ↦ ?_
    obtain ⟨a, k⟩ := q
    simp only [D]
    induction c a with
    | nil => rfl
    | cons b l ih => simp only [List.foldr_cons, List.any_cons, ih]
  have hp : Partrec fun a ↦ Nat.rfind fun k ↦ Part.some (D a k) :=
    Partrec.rfind hD.to_comp.partrec₂
  refine hp.dom_re.of_eq fun a ↦ ?_
  refine Nat.rfind_dom.trans ?_
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  constructor
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb, hsome⟩ := List.any_eq_true.mp hk.symm
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hsome
    exact ⟨b, hb, (hdom a b).mp
      (Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_complete.mpr ⟨k, hx⟩⟩)⟩
  · rintro ⟨b, hb, hRab⟩
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp ((hdom a b).mpr hRab)
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
    exact ⟨k, (List.any_eq_true.mpr ⟨b, hb, Option.isSome_iff_exists.mpr ⟨x, hk⟩⟩).symm⟩

/-- **Bounded universal quantification preserves recursive enumerability.** Let $\alpha$ and
$\beta$ be types with primitive recursive encodings into $\mathbb{N}$, let $R$ be a relation
between $\alpha$ and $\beta$ that is recursively enumerable as a predicate on pairs $(a, b)$, and
let $c$ be a primitive recursive function sending each $a \in \alpha$ to a finite list $c(a)$ of
elements of $\beta$. Then the predicate $a \mapsto \forall b \in c(a),\ R(a, b)$ is recursively
enumerable.

The proof searches for one step bound $k$ at which the simulation of the semi-decision procedure
for $R$ halts on $(a, b)$ for every $b$ in $c(a)$; the step-bounded simulation is monotone in $k$.
-/
theorem REPred.forall_mem {β : Type*} [Primcodable β] {R : α → β → Prop}
    (hR : REPred fun p : α × β ↦ R p.1 p.2) {c : α → List β} (hc : Primrec c) :
    REPred fun a ↦ ∀ b ∈ c a, R a b := by
  obtain ⟨code, hcode⟩ := Nat.Partrec.Code.exists_code.1 hR
  have hdom : ∀ a b, (Nat.Partrec.Code.eval code (Encodable.encode (a, b))).Dom ↔ R a b := by
    intro a b
    rw [hcode]
    simp only [Encodable.encodek, Part.coe_some, Part.bind_some, Part.map_Dom]
    exact ⟨fun ⟨h, _⟩ ↦ h, fun h ↦ ⟨h, trivial⟩⟩
  let D : α → ℕ → Bool := fun a k ↦ (c a).all fun b ↦
    (Nat.Partrec.Code.evaln k code (Encodable.encode (a, b))).isSome
  have hD : Primrec₂ D := by
    have hg : Primrec fun q : (α × ℕ) × β ↦
        (Nat.Partrec.Code.evaln q.1.2 code (Encodable.encode (q.1.1, q.2))).isSome :=
      Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
        (Primrec.pair (Primrec.snd.comp Primrec.fst) (Primrec.const code))
        (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst) Primrec.snd))))
    refine (Primrec.list_foldr (hc.comp Primrec.fst) (Primrec.const true)
      (Primrec.and.comp (hg.comp (Primrec.pair Primrec.fst (Primrec.fst.comp Primrec.snd)))
        (Primrec.snd.comp Primrec.snd)).to₂).of_eq fun q ↦ ?_
    obtain ⟨a, k⟩ := q
    simp only [D]
    induction c a with
    | nil => rfl
    | cons b l ih => simp only [List.foldr_cons, List.all_cons, ih]
  have hp : Partrec fun a ↦ Nat.rfind fun k ↦ Part.some (D a k) :=
    Partrec.rfind hD.to_comp.partrec₂
  refine hp.dom_re.of_eq fun a ↦ ?_
  refine Nat.rfind_dom.trans ?_
  simp only [Part.mem_some_iff, Part.some_dom, implies_true, and_true]
  constructor
  · rintro ⟨k, hk⟩ b hb
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp hk.symm b hb)
    exact (hdom a b).mp (Part.dom_iff_mem.mpr ⟨x, Nat.Partrec.Code.evaln_complete.mpr ⟨k, hx⟩⟩)
  · intro hall
    -- a step bound for each candidate, then their maximum
    have hk : ∀ b ∈ c a, ∃ k, (Nat.Partrec.Code.evaln k code (Encodable.encode (a, b))).isSome :=
      fun b hb ↦ by
        obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp ((hdom a b).mpr (hall b hb))
        obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hx
        exact ⟨k, Option.isSome_iff_exists.mpr ⟨x, hk⟩⟩
    choose! kb hkb using hk
    refine ⟨((c a).map kb).foldr max 0, (List.all_eq_true.mpr fun b hb ↦ ?_).symm⟩
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp (hkb b hb)
    refine Option.isSome_iff_exists.mpr ⟨x, Nat.Partrec.Code.evaln_mono ?_ hx⟩
    exact List.le_max_of_le' 0 (List.mem_map_of_mem hb) le_rfl

/-- **Searching a computable list with a computable test is computable.** Let $\gamma$ and
$\beta$ be types with primitive recursive encodings into $\mathbb{N}$, let $l$ be a computable
function sending each $x \in \gamma$ to a finite list $l(x)$ of elements of $\beta$, and let $g$
be a computable Boolean-valued function of $x \in \gamma$ and $b \in \beta$. Then the
Boolean-valued function that sends $x$ to true exactly when $g(x, b)$ is true for some $b$ in
$l(x)$ is computable.

The proof scans the indices of $l(x)$ by primitive recursion. -/
theorem computable_list_any {γ β : Type*} [Primcodable γ] [Primcodable β]
    {l : γ → List β} {g : γ → β → Bool} (hl : Computable l) (hg : Computable₂ g) :
    Computable fun x ↦ (l x).any (g x) := by
  have key : ∀ (m : List β) (t : β → Bool) (n : ℕ),
      Nat.rec (motive := fun _ ↦ Bool) false (fun i acc ↦ acc || (m[i]?).elim false t) n =
        true ↔ ∃ i < n, ∃ b, m[i]? = some b ∧ t b = true := by
    intro m t n
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [Bool.or_eq_true, ih]
      constructor
      · rintro (⟨i, hi, h⟩ | h)
        · exact ⟨i, by omega, h⟩
        · cases hm : m[n]? with
          | none => simp [hm] at h
          | some b => exact ⟨n, by omega, b, hm, by simpa [hm] using h⟩
      · rintro ⟨i, hi, b, hb, ht⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
        · exact Or.inl ⟨i, hi, b, hb, ht⟩
        · exact Or.inr (by simp [hb, ht])
  have hc : Computable fun x ↦ Nat.rec (motive := fun _ ↦ Bool) false
      (fun i acc ↦ acc || ((l x)[i]?).elim false (g x)) (l x).length := by
    refine Computable.nat_rec (h := fun x p ↦ p.2 || ((l x)[p.1]?).elim false (g x))
      (Computable.list_length.comp hl) (Computable.const false) ?_
    refine (Primrec.or.to_comp).comp (Computable.snd.comp Computable.snd) ?_
    refine (Computable.option_casesOn
      (Computable.list_getElem?.comp (hl.comp Computable.fst)
        (Computable.fst.comp Computable.snd))
      (Computable.const false) (hg.comp (Computable.fst.comp Computable.fst)
        Computable.snd).to₂).of_eq fun q ↦ ?_
    cases (l q.1)[q.2.1]? <;> rfl
  refine hc.of_eq fun x ↦ Bool.eq_iff_iff.mpr ?_
  rw [key, List.any_eq_true]
  constructor
  · rintro ⟨i, -, b, hb, hgb⟩
    exact ⟨b, List.mem_of_getElem? hb, hgb⟩
  · rintro ⟨b, hb, hgb⟩
    obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hb
    exact ⟨i, (List.getElem?_eq_some_iff.mp hi).1, b, hi, hgb⟩

/-- **Selection for r.e. relations.** Let $\alpha$ and $\beta$ be types with primitive recursive
encodings into $\mathbb{N}$, and let $R$ be a relation between $\alpha$ and $\beta$ that is
recursively enumerable as a predicate on pairs $(a, b)$. Then there is a partial recursive
function $g$ from $\alpha$ to $\beta$ such that, for every $a \in \alpha$, if $g(a)$ is defined
then its value $b$ satisfies $R(a, b)$, and $g(a)$ is defined whenever some $b \in \beta$
satisfies $R(a, b)$.

The proof searches over pairs of a candidate $b$ and a step bound by dovetailing with the
step-bounded simulation of the semi-decision procedure for $R$. -/
theorem REPred.exists_partrec_choose {β : Type*} [Primcodable β] {R : α → β → Prop}
    (hR : REPred fun p : α × β ↦ R p.1 p.2) :
    ∃ g : α →. β, Partrec g ∧ (∀ a b, b ∈ g a → R a b) ∧ ∀ a, (∃ b, R a b) → (g a).Dom := by
  have hG : Partrec fun n : ℕ ↦ (Part.ofOption (Encodable.decode₂ (α × β) n)).bind fun p ↦
      (Part.assert (R p.1 p.2) fun _ ↦ Part.some ()).map fun _ ↦ (0 : ℕ) :=
    Partrec.bind (Computable.ofOption Primrec.decode₂.to_comp)
      ((hR.comp Computable.snd).map (Computable.const 0).to₂)
  obtain ⟨c, hc⟩ := Nat.Partrec.Code.exists_code.1 (Partrec.nat_iff.1 hG)
  have hspec : ∀ p : α × β, (c.eval (Encodable.encode p)).Dom ↔ R p.1 p.2 := fun p ↦ by
    rw [hc]
    simp [Part.assert]
  let test : α → ℕ → Bool := fun a m ↦
    ((Encodable.decode (α := β) m.unpair.1).map fun b ↦
      (Nat.Partrec.Code.evaln m.unpair.2 c (Encodable.encode (a, b))).isSome).getD false
  have htest : Primrec₂ test :=
    Primrec.option_getD.comp
      (Primrec.option_map (Primrec.decode.comp (Primrec.fst.comp (Primrec.unpair.comp
        Primrec.snd)))
        (Primrec.option_isSome.comp (Nat.Partrec.Code.primrec_evaln.comp (Primrec.pair
          (Primrec.pair (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst)))
            (Primrec.const c))
          (Primrec.encode.comp (Primrec.pair (Primrec.fst.comp Primrec.fst)
            Primrec.snd))))).to₂)
      (Primrec.const false)
  -- a found index decodes to a witness
  have hfound : ∀ a m, test a m = true → ∃ b, Encodable.decode (α := β) m.unpair.1 = some b ∧
      R a b := by
    intro a m hm
    simp only [test] at hm
    cases hb : Encodable.decode (α := β) m.unpair.1 with
    | none => simp [hb] at hm
    | some b =>
      simp only [hb, Option.map_some, Option.getD_some] at hm
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
      exact ⟨b, rfl, (hspec (a, b)).mp
        (Part.dom_iff_mem.mpr ⟨v, Nat.Partrec.Code.evaln_sound hv⟩)⟩
  refine ⟨fun a ↦ (Nat.rfind fun m ↦ Part.some (test a m)).bind fun m ↦
      Part.ofOption (Encodable.decode (α := β) m.unpair.1),
    Partrec.bind (Partrec.rfind htest.to_comp.partrec₂)
      (Computable.ofOption (Computable.decode.comp (Computable.fst.comp
        (Computable.unpair.comp Computable.snd)))).to₂, fun a b hb ↦ ?_, fun a ⟨b, hb⟩ ↦ ?_⟩
  · obtain ⟨m, hm, hbm⟩ := Part.mem_bind_iff.mp hb
    have hspec' := Nat.rfind_spec hm
    simp only [Part.mem_some_iff] at hspec'
    obtain ⟨b', hb', hR'⟩ := hfound a m hspec'.symm
    rw [hb', Part.mem_ofOption, Option.mem_def, Option.some_inj] at hbm
    exact hbm ▸ hR'
  · obtain ⟨v, hv⟩ := Part.dom_iff_mem.mp ((hspec (a, b)).mpr hb)
    obtain ⟨k, hk⟩ := Nat.Partrec.Code.evaln_complete.mp hv
    have htrue : test a (Nat.pair (Encodable.encode b) k) = true := by
      simp only [test, Nat.unpair_pair, Encodable.encodek, Option.map_some, Option.getD_some]
      exact Option.isSome_iff_exists.mpr ⟨v, hk⟩
    have hd : (Nat.rfind fun m ↦ Part.some (test a m)).Dom :=
      Nat.rfind_dom.mpr ⟨_, by simpa using htrue, fun _ ↦ trivial⟩
    have hm := Part.get_mem hd
    have hspec' := Nat.rfind_spec hm
    simp only [Part.mem_some_iff] at hspec'
    obtain ⟨b', hb', -⟩ := hfound a _ hspec'.symm
    exact ⟨hd, by simp [hb']⟩

/-- **Existential projection preserves recursive enumerability.** Let $\alpha$ and $\beta$ be
types with primitive recursive encodings into $\mathbb{N}$, and let $R$ be a relation between
$\alpha$ and $\beta$ that is recursively enumerable as a predicate on pairs $(a, b)$. Then the
predicate $a \mapsto \exists b \in \beta,\ R(a, b)$ is recursively enumerable.

The predicate is the domain of the partial recursive function that selects a witness of $R$. -/
theorem REPred.exists {β : Type*} [Primcodable β] {R : α → β → Prop}
    (hR : REPred fun p : α × β ↦ R p.1 p.2) : REPred fun a ↦ ∃ b, R a b := by
  obtain ⟨g, hg, hsound, hdom⟩ := REPred.exists_partrec_choose hR
  refine hg.dom_re.of_eq fun a ↦ ⟨fun h ↦ ?_, hdom a⟩
  obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp h
  exact ⟨b, hsound a b hb⟩

end MetaMathlibExt
