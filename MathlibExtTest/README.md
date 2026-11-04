# MathlibExtTest

`MathlibExtTest` contains tests, benchmarks, and diagnostics for public
`MathlibExt` APIs. It may import `MathlibExt`, but production libraries must
not import it.

Tests should exercise meaningful public behavior, including boundary values,
typeclass inference, simplification, and expected elaboration failures when
those protect against plausible regressions.

## Runtime witness coverage

| API and canonical relation | Runtime client and measured coverage | Reproduce |
| --- | --- | --- |
| Mathlib [`RegularExpression.rmatch` / `rmatch_iff_matches'`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/Computability/RegularExpressions.lean#L177): whole-word matching | [RegularExpressionTests](Computability/RegularExpressionTests.lean): 8 fixed expressions covering all constructors and nullable concatenation; 11 fixed + 511 exhaustive + 1,000 generated words per expression, 12,176 checks; one shared generated corpus, length ≤ 12, seed 2026110403 | [Command below](#reproduce-runtime-coverage) |

The independent oracles inspect word shape, never decidable `matches'` membership
(which calls `rmatch`). The small theorem consumer is separate proof-interface
evidence. Runtime counts are not theorems.

## Reproduce runtime coverage

After `lake --wfail build MathlibExtTest.Computability.RegularExpressionTests`,
re-execute the assertions and print measured corpus and branch counts:

```sh
lake env lean -DwarningAsError=true MathlibExtTest/Computability/RegularExpressionTests.lean
```
