---
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.shiftedPadovan_infinite_not_isSumOfTwoPrimePowers
---

# Shifted Padovan infinite not is Sum Of Two Prime Powers

Infinitely many Padovan numbers are not a sum of two prime powers.
Stated for the repository shifted Padovan sequence (`1, 0, 1`, with
`shiftedPadovanSequence (n + 2)` equal to the standard Padovan number
`P_n` with initial values `1, 1, 1`), so the infinitude content agrees
with the paper's. The paper's strengthening to every sufficiently
large `k ≡ 45750 (mod 967206240)` is omitted for the same
seed-convention reason as in the Tribonacci statement.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.ThirdOrderPrimePowersWanted](../../../../../sources/v2/WantedExt.md)
- Baczkowski and Keener, *Third-Order Recurrence Sequences with Infinitely Many Terms not Equal to the Sum of Two Prime Powers*, Journal of Integer Sequences 29 (2026), Article 26.2.3, Theorem 3 (`jis-2026-26.2.3-thm-3`).
