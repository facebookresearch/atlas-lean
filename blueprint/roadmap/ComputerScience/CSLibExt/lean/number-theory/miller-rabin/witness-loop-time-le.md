---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.MillerRabin.witnessLoop_time_le
---

# Witness Loop time le

CLRS `MILLER-RABIN(n, s)` with the bases given explicitly: `false` (*composite*) as soon as a
base is a witness, `true` (*prime*) otherwise. The caller supplies bases in `1, …, n - 1`, as
CLRS's `RANDOM(1, n - 1)` does; only then is a *composite* answer guaranteed correct
(`not_prime_of_millerRabin_eq_false`). -/
def millerRabin (n : ℕ) : List ℕ → TimeM ℕ Bool
  | [] => pure true
  | a :: as => do
      let w ← witness a n
      if w then pure false else millerRabin n as

/-! ## Cost

## Depends on

- [Witness Loop](witness-loop.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.NumberTheory.MillerRabin](../../../../../../sources/v2/CSLibExt.md)
