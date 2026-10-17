---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.karatsuba_time
---

# Karatsuba time

For an input below `B^n`, its high part, low part and their difference are below `B^⌈n/2⌉`.
Applied to both inputs, all six recursive operands stay within the digit model, and the base case
multiplies single digits. -/
theorem karatsuba_operands_lt {B n x : ℕ} (hB : 0 < B) (hx : x < B ^ n) :
    x / B ^ ((n + 1) / 2) < B ^ ((n + 1) / 2) ∧ x % B ^ ((n + 1) / 2) < B ^ ((n + 1) / 2) ∧
      Nat.dist (x / B ^ ((n + 1) / 2)) (x % B ^ ((n + 1) / 2)) < B ^ ((n + 1) / 2) := by
  set m := (n + 1) / 2
  have hpos : 0 < B ^ m := Nat.pow_pos hB
  have hdiv : x / B ^ m < B ^ m := by
    rw [Nat.div_lt_iff_lt_mul hpos, ← pow_add]
    exact hx.trans_le (Nat.pow_le_pow_right hB (by omega))
  have hmod : x % B ^ m < B ^ m := Nat.mod_lt _ hpos
  refine ⟨hdiv, hmod, ?_⟩
  rw [Nat.dist_eq_max_sub_min]
  exact lt_of_le_of_lt (Nat.sub_le _ _) (max_lt hdiv hmod)

/-! ## Cost

## Depends on

- [Karatsuba](karatsuba.md)
- [Karatsuba Cost](karatsuba-cost.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba](../../../../../../sources/v2/CSLibExt.md)
