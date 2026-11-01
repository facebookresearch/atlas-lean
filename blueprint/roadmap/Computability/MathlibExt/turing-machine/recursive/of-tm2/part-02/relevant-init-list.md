---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Recursive.relevant_initList
---

# Relevant init List

The coded run follows the machine's run, and every configuration on it has relevant
symbols. -/
theorem optStepC_iterate (j : ℕ) {o : Option tm.Cfg} (ho : ∀ c ∈ o, Relevant tm c.stk) :
    (optStepC tm)^[j] (o.map (enc tm)) = ((flip bind tm.step)^[j] o).map (enc tm) ∧
      ∀ c ∈ (flip bind tm.step)^[j] o, Relevant tm c.stk := by
  induction j generalizing o with
  | zero => exact ⟨rfl, ho⟩
  | succ j ih =>
    have hstep : optStepC tm (o.map (enc tm)) = (flip bind tm.step o).map (enc tm) ∧
        ∀ c ∈ flip bind tm.step o, Relevant tm c.stk := by
      cases o with
      | none => exact ⟨rfl, fun c hc ↦ by cases hc⟩
      | some c =>
        obtain ⟨h₁, h₂⟩ := stepC_enc tm (ho c rfl)
        exact ⟨h₁, h₂⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hstep.1]
    exact ih hstep.2

/-! ### Input, output and halting

## Depends on

- [Relevant](../part-01/relevant-2.md)

## Proof depends on

- [Pushes](../part-01/pushes.md)
- [Relevant](../part-01/relevant.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Recursive.OfTM2](../../../../../../../sources/v2/MathlibExt.md)
