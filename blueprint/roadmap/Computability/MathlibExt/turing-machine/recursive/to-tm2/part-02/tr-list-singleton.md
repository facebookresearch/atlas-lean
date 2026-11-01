---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.trList_singleton
---

# Tr List singleton

The main phase: `tr` evaluates `c` on `[n]`, and the wrapped machine follows it into the
post-phase. -/
theorem main_phase {f : ℕ → ℕ} (hc : ∀ n, c.eval [n] = pure [f n]) (n : ℕ) :
    ∃ N, frun c N (some ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
        mkStk (trList [n]) [] [] [] [] []⟩) =
      some ⟨some (Sum.inl Phase.post1), none, mkStk (trList [f n]) [] [] [] [] []⟩ := by
  have heval := tr_eval c [n]
  rw [hc n] at heval
  have hmem : halt [f n] ∈ StateTransition.eval (TM2.step tr) (init c [n]) := by
    rw [heval]
    exact Part.mem_map _ (Part.mem_some _)
  obtain ⟨N, hN⟩ := exists_iterate_eq_of_reaches (StateTransition.mem_eval.mp hmem).1
  have h₀ : TrRel c (init c [n]) ⟨some (Sum.inr ⟨trNormal c Cont'.halt, start_mem c⟩), none,
      mkStk (trList [n]) [] [] [] [] []⟩ := ⟨rfl, rfl, start_mem c, rfl⟩
  obtain ⟨⟨dl, dv, ds⟩, hd, hv, hs, hl⟩ := run_rel c h₀ N hN
  refine ⟨N, hd.trans ?_⟩
  simp only [halt] at hv hs hl
  simp only [LabelRel] at hl
  subst hv hs hl
  rfl

/-! ### Assembly

## Depends on

- [Bool ToΓ'](../part-01/bool-to.md)

## Proof depends on

- [Tr Nat eq map](../part-01/tr-nat-eq-map.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.ToTM2](../../../../../../../sources/v2/MathlibExt.md)
