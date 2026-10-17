---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Logic.PL.BDD.size_pos
---

# Size pos

Fixing the top variable of an ordered node selects a child. -/
theorem eval_update_node {n v : Nat} {lo hi : BDD} (h : OrderedFrom n (node v lo hi))
    (σ : Nat → Bool) (b : Bool) :
    (node v lo hi).eval (Function.update σ v b) = if b then hi.eval σ else lo.eval σ := by
  rw [eval_node, Function.update_self, eval_update_of_lt h.2.2 (by omega),
    eval_update_of_lt h.2.1 (by omega)]

/-! ### Canonicity

## Depends on

- [BDD](bdd.md)
- [Size](size.md)

## Sources

- [CSLibExt, CSLibExt.Logics.Propositional.BDD.Basic](../../../../../../sources/v2/CSLibExt.md)
