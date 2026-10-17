---
article_id: af_fa3667da163a74c29bd8895d
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.no_collatz_m_cycle_le_ninety_one
---

# No Collatz MCycle Wanted

No Collatz m-cycle with `m ≤ 91`.

`C` is the shortcut Collatz operator (`n/2` for even `n`, `(3n+1)/2` for
odd `n`); a cycle is nontrivial when every orbit entry exceeds 2 (the
trivial cycle is `1, 2, 1, 2, …`), has minimal period `p`, and is an
m-cycle when exactly `m` positions lie cyclically strictly below both
neighbours.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.Sequences.NoCollatzMCycleWanted](../../../../../sources/v2/WantedExt.md)
- Christian Hercher, "There are no Collatz m-Cycles with m ≤ 91," Journal of Integer Sequences 26 (2023), Article 23.3.5, Main Theorem (label Theorem17), lines 541–543, https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.tex with the operator at lines 104–111 and the m-cycle definition at lines 149–151.
