/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.RigidEUnificationDefs

namespace MetaMathlibExt.Complexity.NPComplete.RigidEUnification

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)
open FirstOrder FirstOrder.Language
open MetaMathlibExt.Complexity.NPComplete.UnificationForFinitelyPresentedAlgebras (lang tokens)

private theorem accepts_encoding (i : RigidEUnificationInstance) :
    rigidEUnificationDec (bitEncode i) = true ↔ WellFormed i ∧ RigidEUnificationFeasible i := by
  simp [rigidEUnificationDec, bitDecode_bitEncode]

/-- A single unary function symbol `f` (symbol `0`). -/
private abbrev ar : List ℕ := [1]

private abbrev symF : (lang ar).Functions 1 := ⟨⟨0, by decide⟩, rfl⟩

/-- `f(t)`. -/
private abbrev tmF {α : Type} (t : (lang ar).Term α) : (lang ar).Term α :=
  Term.func symF fun _ => t

/-- Token lists determine terms: the token map is injective on symbols, since a symbol index
fixes its arity. -/
private theorem tokens_injective {n : ℕ} :
    Function.Injective (tokens (ar := ar) (α := Fin n) Fin.val) := by
  intro s s' h
  refine Term.listEncode_injective (List.map_injective_iff.2 ?_ h)
  rintro (a | ⟨l, f⟩) (b | ⟨l', f'⟩) hab
  · simp only [Sum.elim_inl, Prod.mk.injEq, true_and] at hab
    exact congrArg _ (Fin.ext hab)
  · simp at hab
  · simp at hab
  · -- `ar` has a single symbol, so the two symbols agree, and with them their arities
    have hf : f.1 = f'.1 := Fin.ext (by simp)
    have hl : l = l' := f.2.symm.trans (hf ▸ f'.2)
    subst hl
    obtain rfl : f = f' := Subtype.ext hf
    rfl

/-- The natural numbers with `f` read as the successor function. -/
private instance : (lang ar).Structure ℕ where
  funMap _ xs := (List.ofFn xs).sum + 1
  RelMap r _ := r.elim

/-- With variables `{v₀}`, unify `s = v₀` with `t = f(v₀)` under the equations `E`. -/
private abbrev problem (E : List (List (ℕ × ℕ) × List (ℕ × ℕ))) : RigidEUnificationInstance :=
  (ar, 1, E, [(0, 0)], [(1, 0), (0, 0)])

/-- A lone continuation bit is a truncated instance encoding. -/
example : rigidEUnificationDec [true] = false := by
  have h : bitDecode (α := RigidEUnificationInstance) [true] = none := rfl
  simp [rigidEUnificationDec, h]

/-- With the equation `f(v₀) = v₀`, the identity substitution is a rigid unifier of `v₀` and
`f(v₀)`. -/
example : rigidEUnificationDec (bitEncode (problem [([(1, 0), (0, 0)], [(0, 0)])])) = true := by
  apply (accepts_encoding _).2
  have hE : Equations (problem [([(1, 0), (0, 0)], [(0, 0)])])
      [(tmF (Term.var 0), Term.var 0)] := rfl
  have hs : tokens Fin.val (Term.var 0 : (lang ar).Term (Fin 1)) = [(0, 0)] := rfl
  have ht : tokens Fin.val (tmF (Term.var 0) : (lang ar).Term (Fin 1)) = [(1, 0), (0, 0)] :=
    rfl
  refine ⟨⟨⟨_, hE⟩, ⟨_, hs⟩, ⟨_, ht⟩⟩, _, hE, _, _, hs, ht, Term.var, ?_⟩
  intro M _ v hEv
  exact (hEv _ List.mem_cons_self).symm

/-- With no equations, `σ(v₀) = f(σ(v₀))` fails in the natural numbers with `f` the successor,
for every substitution `σ`. -/
example : rigidEUnificationDec (bitEncode (problem [])) = false := by
  rw [Bool.eq_false_iff]
  intro hacc
  obtain ⟨-, E, hE, s, t, hs, ht, σ, hent⟩ := (accepts_encoding _).1 hacc
  have hE0 : E = [] := List.map_eq_nil_iff.1 hE
  have hs' : s = Term.var 0 := tokens_injective (hs.trans rfl)
  have ht' : t = tmF (Term.var 0) := tokens_injective (ht.trans rfl)
  subst hE0 hs' ht'
  have h := hent ℕ (fun _ => 0) (by simp)
  change _ = (List.ofFn fun _ : Fin 1 => Term.realize (fun _ => (0 : ℕ)) (σ 0)).sum + 1 at h
  simp at h

/-- The no-instance above is well formed, so it is rejected for infeasibility. -/
example : WellFormed (problem []) :=
  ⟨⟨[], rfl⟩, ⟨Term.var 0, rfl⟩, ⟨tmF (Term.var 0), rfl⟩⟩

end MetaMathlibExt.Complexity.NPComplete.RigidEUnification
