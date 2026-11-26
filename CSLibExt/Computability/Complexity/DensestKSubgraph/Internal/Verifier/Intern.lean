/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Computability.Complexity.SatLookup
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import MathlibExt.Computability.TuringMachine.StackEmbedding

/-! # Lookup-or-insert on bounded dictionaries of binary words -/

@[expose] public section

namespace Cslib.Complexity.DensestKSubgraph.Internal.Intern

open Turing Function MetaMathlibExt.TM2Program MetaMathlibExt.TM2Embedding
open Cslib.Complexity.SatVerifier Cslib.Complexity.PolynomialEncoding

/- The existing SAT lookup layout plus a raw query stack and one temporary stack. -/
inductive K | lookup (k : Lookup.K) | query | temp
  deriving DecidableEq

instance : Fintype K where
  elems := {K.query, .temp} ∪ Finset.univ.image K.lookup
  complete k := by cases k <;> simp

/- The raw query is in forward order; lookup uses tagged bit symbols. -/
@[reducible] def Γ : K → Type
  | .query => Bool
  | _ => Sym

/- Lookup returns a bit; only a missing key is added. -/
inductive Lab | read | lookup (l : Lookup.Lab) | answer | flip | insert | marker
  | restore (old : Bool) | done (old : Bool)
  deriving DecidableEq

instance : Fintype Lab where
  elems := {Lab.read, .answer, .flip, .insert, .marker, .restore true, .restore false,
    .done true, .done false} ∪ Finset.univ.image Lab.lookup
  complete l := by
    cases l with
    | restore b | done b => cases b <;> simp
    | _ => simp

/- Preserve the entire lookup table layout while running the verified lookup component. -/
def emb : SEmb (fun _ : Lookup.K => Sym) Γ where
  e := K.lookup
  inj _ _ h := K.lookup.inj h
  ι _ := Equiv.refl _

/- Resume after lookup at the answer dispatch. -/
def redirect : Lookup.Lab → Lab
  | .done => .answer
  | l => .lookup l

/- The insertion path copies the reversed query to the top of the table and adds its marker. -/
def prog : Lab → TM2.Stmt Γ Lab Bool
  | .read => moveB .query (.lookup .T) some Sym.bit .read (.lookup .init)
  | .lookup l => mapS emb redirect (Lookup.prog l)
  | .answer => .pop (.lookup .V) (fun _ o => bitOf Sym.bit? o) <| .branch id
      (.goto fun _ => .restore true) (.goto fun _ => .flip)
  | .flip => moveB (.lookup .T) .temp Sym.bit? Sym.bit .flip .insert
  | .insert => splitB .temp (.lookup .T) (.lookup .B) Sym.bit? Sym.bit Sym.bit .insert .marker
  | .marker => emit (.lookup .B) [.val true] (.restore false)
  | .restore b => moveB (.lookup .T) .query Sym.bit? id (.restore b) (.done b)
  | .done _ => .halt

private theorem embeds : Embeds emb redirect Lookup.prog prog := by
  intro l
  cases l <;> first | exact Or.inl rfl | exact Or.inr rfl

/- A key is live iff present, since each table entry has value `true`. -/
def ents (keys : List (List Bool)) : List Ent := keys.map fun q => (q, some true)

private theorem liveVal_ents (keys : List (List Bool)) (q : List Bool) :
    liveVal (ents keys) q = decide (q ∈ keys) := by
  induction keys with
  | nil => rfl
  | cons a keys ih =>
    by_cases h : a = q
    · simp [ents, liveVal, h]
    · simpa [ents, liveVal, h, Ne.symm h] using ih

private theorem tblStk_push (keys : List (List Bool)) (q : List Bool) :
    tblStk (ents (keys ++ [q])) = .val true :: (q.map Sym.bit).reverse ++ tblStk (ents keys) := by
  simp [ents, tblStk, entToks, markOf]

/- Exact invariant of an idle dictionary, including the preserved raw query. -/
def st (q : List Bool) (keys : List (List Bool)) : (k : K) → List (Γ k)
  | .query => q
  | .lookup .B => tblStk (ents keys)
  | _ => []

private theorem read_run (q : List Bool) (keys : List (List Bool)) (v : Bool) :
    ∃ w, Run prog (q.length + 1) ⟨some .read, v, st q keys⟩
      ⟨some (.lookup .init), w, update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse⟩ := by
  obtain ⟨w, T, h, hq, ht, hf⟩ := moveB_run (M := prog) (self := .read) rfl (by decide)
    q q [] v (st q keys) (by simp [st]) rfl rfl
  have he : T = update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse := by
    funext k
    cases k with
    | query => exact hq
    | temp => exact hf _ (by decide) (by decide)
    | lookup k =>
      cases k with
      | T => simpa [st] using ht
      | _ => exact hf _ (by decide) (by decide)
  exact ⟨w, he ▸ h⟩

private theorem lookup_run (q : List Bool) (keys : List (List Bool)) (v : Bool) :
    RunLe prog (8 * (tblStk (ents keys)).length + 5)
      ⟨some (.lookup .init), v, update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse⟩
      ⟨some (if q ∈ keys then .restore true else .flip), decide (q ∈ keys),
        update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse⟩ := by
  let S := update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse
  let U := Lookup.stk (q.map Sym.bit).reverse (tblStk (ents keys)) [] [] [] []
  obtain ⟨w, hr⟩ := Lookup.run q (ents keys) [] rfl v U
    (by simp [U]) rfl rfl rfl rfl rfl
  obtain ⟨T, r₁, ha, hf⟩ := runLe_embed redirect embeds hr (S' := S) (by
    intro k
    change S (.lookup k) = List.map id (U k)
    rw [List.map_id]
    cases k <;> rfl)
  have he : T = update S (.lookup .V) [Sym.bit (decide (q ∈ keys))] := by
    funext k
    cases k with
    | query | temp => exact hf _ (by simp [emb])
    | lookup j =>
      have hc := ha j
      change T (.lookup j) = List.map id (update U .V [Sym.bit (liveVal (ents keys) q)] j) at hc
      rw [List.map_id, liveVal_ents] at hc
      rw [hc]
      cases j <;> rfl
  rw [he] at r₁
  have r₂ : Run prog 1
      ⟨some .answer, w, update S (.lookup .V) [Sym.bit (decide (q ∈ keys))]⟩
      ⟨some (if q ∈ keys then .restore true else .flip), decide (q ∈ keys), S⟩ := by
    have hv : S (.lookup .V) = [] := rfl
    apply Run.single
    by_cases h : q ∈ keys <;>
      simp [prog, TM2.stepAux, bitOf, Lookup.bit?_bit, h, ← hv, update_eq_self]
  exact (r₁.trans (r₂.le le_rfl)).mono (by omega)

private theorem finish (b : Bool) (q : List Bool) (keys : List (List Bool)) (v : Bool) :
    ∃ w, Run prog (q.length + 1)
      ⟨some (.restore b), v, update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse⟩
      ⟨some (.done b), w, st q keys⟩ := by
  obtain ⟨w, T, hr, ht, hq, hf⟩ := moveB_run (M := prog) (self := .restore b) rfl (by decide)
    q.reverse (q.map Sym.bit).reverse [] v
    (update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse)
    (by simp) (Lookup.isBitBlock_rev q) rfl
  have he : T = st q keys := by
    funext j
    cases j with
    | query => simpa [st] using hq
    | temp => exact hf _ (by decide) (by decide)
    | lookup k =>
      cases k with
      | T => exact ht
      | _ => exact hf _ (by decide) (by decide)
  exact ⟨w, he ▸ hr.of_eq (by simp)⟩

private theorem insert_run (q : List Bool) (keys : List (List Bool)) (v : Bool) :
    RunLe prog (2 * q.length + 3)
      ⟨some .flip, v, update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse⟩
      ⟨some (.restore false), false,
        update (st [] (keys ++ [q])) (.lookup .T) (q.map Sym.bit).reverse⟩ := by
  let S := update (st [] keys) (.lookup .T) (q.map Sym.bit).reverse
  obtain ⟨w, U, hr, ht, hb, hf⟩ := moveB_run (M := prog) (self := .flip)
    rfl (by decide) q.reverse (q.map Sym.bit).reverse [] v S (by simp [S])
    (Lookup.isBitBlock_rev q) rfl
  have hb' : U .temp = q.map Sym.bit := by simpa [S, st] using hb
  obtain ⟨V, rr, htmp, ht', hB, hk⟩ := splitB_run (M := prog) (self := .insert)
    rfl (by decide) (by decide) (by decide) Sym.bit Lookup.bit?_bit q [] w U rfl (by simp [hb'])
  have hB' : V (.lookup .B) = (q.map Sym.bit).reverse ++ tblStk (ents keys) := by
    rw [hB, hf _ (by decide) (by decide)]
    rfl
  have r₃ := emit_run (M := prog) (self := .marker) rfl false V
  have hfin : update V (.lookup .B) ([Sym.val true].reverse ++ V (.lookup .B)) =
      update (st [] (keys ++ [q])) (.lookup .T) (q.map Sym.bit).reverse := by
    funext j
    cases j with
    | query => exact (hk _ (by decide) (by decide) (by decide)).trans (hf _ (by decide) (by decide))
    | temp => exact htmp
    | lookup k =>
      cases k with
      | B =>
        rw [update_self, hB']
        change Sym.val true :: (q.map Sym.bit).reverse ++ tblStk (ents keys) =
          tblStk (ents (keys ++ [q]))
        exact (tblStk_push keys q).symm
      | T => simpa [ht] using ht'
      | _ => exact (hk _ (by decide) (by decide) (by decide)).trans (hf _ (by decide) (by decide))
  rw [hfin] at r₃
  exact ((hr.trans rr).trans r₃).le (by simp; omega)

/- The existing key table remains well formed; a missing key is added once. Both outcomes keep
all other stacks in the invariant. The bound is linear in the serialized table and the query. -/
theorem run (q : List Bool) (keys : List (List Bool)) (v : Bool) :
    ∃ w, RunLe prog (8 * (tblStk (ents keys)).length + 4 * q.length + 10)
      ⟨some .read, v, st q keys⟩
      ⟨some (.done (decide (q ∈ keys))), w, st q (if q ∈ keys then keys else keys ++ [q])⟩ := by
  obtain ⟨w, first⟩ := read_run q keys v
  have lookup := lookup_run q keys w
  by_cases h : q ∈ keys
  · simp only [h, ite_true, decide_true] at lookup ⊢
    obtain ⟨y, last⟩ := finish true q keys true
    exact ⟨y, (((first.le le_rfl).trans lookup).trans (last.le le_rfl)).mono (by omega)⟩
  · simp only [h, ite_false, decide_false] at lookup ⊢
    obtain ⟨y, last⟩ := finish false q (keys ++ [q]) false
    exact ⟨y, ((((first.le le_rfl).trans lookup).trans (insert_run q keys false)).trans
      (last.le le_rfl)).mono (by omega)⟩

end Cslib.Complexity.DensestKSubgraph.Internal.Intern
