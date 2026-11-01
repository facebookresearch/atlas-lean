---
article_id: af_62c9fd825e1a61ef52f8a61a
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.rosser_nthPrime_lower_bound_zeroBased
---

# Rosser Nth Prime Wanted

Zero-based form of Rosser's theorem (1.3): `p_n > n log n` for every
positive integer `n`, specialized at `n = k + 1`. `Nat.nth Nat.Prime k`
is the `(k + 1)`-st prime; at `k = 0` the bound reads `0 < 2`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.PrimeCounting.RosserNthPrimeWanted](../../../../../../sources/v2/WantedExt.md)
- Christian Axler, "New Estimates for the nth Prime Number", Journal of Integer Sequences 22 (2019), Article 19.4.2, equation (1.3) (label `1.3`), line 115, with Rosser's theorem stated at lines 115–120, attributed there to Rosser, <https://cs.uwaterloo.ca/journals/JIS/VOL22/Axler/axler17.tex>.
