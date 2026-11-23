# CSLibExtTest

`CSLibExtTest` contains tests and diagnostics for public `CSLibExt` APIs. It
may import `CSLibExt` and `MathlibExt`, but production libraries must not import
it.

Tests should exercise meaningful public behavior, including boundary values,
simplification, decoding failures, and expected elaboration failures when
those protect against plausible regressions.

## Runtime witness coverage

These clients preserve the existing theorem examples and add asserting execution
against independent finite-data oracles. Runtime counts are not theorems.

| API and canonical relation | Runtime client and measured coverage | Reproduce |
| --- | --- | --- |
| [`kmpSearch`](../CSLibExt/Algorithms/Lean/StringMatching/KnuthMorrisPratt.lean): `kmpSearch_eq_some_iff` / `kmpSearch_eq_none_iff`, least zero-based `MatchAt` offset, including empty patterns | [KnuthMorrisPrattRuntimeTests](Algorithms/Lean/StringMatching/KnuthMorrisPrattRuntimeTests.lean): 16 literal + 3,937 exhaustive binary pairs + 600 stratified Plausible pairs; 4,553 checks against `naiveMatches` `.ret.head?`; seed 2026111901; 138 empty-pattern, 59 empty-text, 2,903 absent, 458 overlength, 601 nonempty-at-zero, 911 later, 643 multiple, 202 overlapping, 863 repeated-pattern, 959 prefix-near-miss input shapes (bins overlap) | [Build and replay commands](Algorithms/Lean/StringMatching/KnuthMorrisPrattRuntimeTests.lean#L31) |
| [`MinHeap.extractMin`](../CSLibExt/Algorithms/Lean/DataStructures/BinaryHeap.lean#L747): `extractMin_eq_none_iff`, `extractMin_cons_elements`, `extractMin_le` | [BinaryHeapTests](Algorithms/Lean/DataStructures/BinaryHeapTests.lean): 4 fixed + 1,000 generated lists; public pushes, both-support multiplicity and minimum checks; length ≤ 12, values 0..7, seed 2026110401 | [Commands below](#reproduce-runtime-coverage) |
| [`Knapsack.solve` / `solve_correct`](../CSLibExt/Algorithms/Lean/DynamicProgramming/Knapsack.lean#L461): returned original-index set is feasible, report equals its value sum, and no feasible subset has greater value | [KnapsackRuntimeTests](Algorithms/Lean/DynamicProgramming/KnapsackRuntimeTests.lean): 16 literal + 1,295 exhaustive + 192 stratified cases; independent powerset enumeration, zero weights/values, duplicates, ties, slack and arbitrary-precision values; seed 2026111902; finite runtime agreement, not a cost bound | `lake --wfail build CSLibExtTest.Algorithms.Lean.DynamicProgramming.KnapsackRuntimeTests`; `lake env lean -DwarningAsError=true CSLibExtTest/Algorithms/Lean/DynamicProgramming/KnapsackRuntimeTests.lean` |
| [`cykAccepts` / `cykAccepts_iff`](../CSLibExt/Computability/Languages/ContextFree/CYK.lean#L382), with full Chomsky-normal-form hypotheses | [ContextFreeCYKTests](Computability/Languages/ContextFreeCYKTests.lean): 10 fixed + 511 exhaustive + 1,000 generated words per `anbn`/`epsAB`; one shared generated corpus, length ≤ 12, seed 2026110402; 10 singleton/empty-rule boundary checks | [Commands below](#reproduce-runtime-coverage) |
| [`decodeCNF` / `decodeCNF_eq_some_iff`](../CSLibExt/Computability/CookLevin.lean#L108): entire input equals the returned formula's encoding | [CookLevinTests](Computability/CookLevinTests.lean): 1,000 generated formulas (≤ 3 clauses, ≤ 4 literals/clause, indices 0..7, seed 2026110404), 4,227 checks including fixed/raw encodings, ordered duplicates, truncations and nonempty suffixes; reuses [tokenizer name guards](Computability/Complexity/SatTokenizerTests.lean#L79) | [Commands below](#reproduce-runtime-coverage) |
| [`EncodedRegex.memB` / `memB_iff`](../CSLibExt/Computability/Decidability/RegularExpression.lean#L721-L726) | [RegularExpressionRuntimeTests](Computability/Decidability/RegularExpressionRuntimeTests.lean): CFG membership against the derivative matcher, 334 comparisons and 8 literal boundary assertions over `Bool`; includes total invalid-reference semantics | [Encoded-regex replay](#encoded-regex-replay) |

## Encoded-regex replay

The encoded-regex client exercises [`EncodedRegex.memB` and `memB_iff`](../CSLibExt/Computability/Decidability/RegularExpression.lean#L721-L726),
the CFG-based implementation, not a second standalone test of Mathlib's matcher.
[`RegularExpressionRuntimeTests`](Computability/Decidability/RegularExpressionRuntimeTests.lean)
compares it with Mathlib's independent derivative matcher: 18 fixed encodings × all
15 Boolean words of length ≤ 3, plus 64 stratified Plausible samples (seed
2026111801, at most 5 nodes and word length 4). The 334 comparisons produce 33
acceptances and 301 rejections; eight further literal assertions pin empty, invalid-child,
concatenation and last-root semantics. The generated root-constructor counts are
`[10, 9, 9, 9, 9, 9, 9]` (zero, epsilon, character, union, concatenation, star, empty),
node-count bins 0..5 are `[9, 12, 12, 12, 12, 7]`, and word-length bins 0..4 are
`[13, 13, 13, 13, 12]`. These are finite `Bool` fixtures and input-shape counts,
not a universal proof, implementation branch instrumentation or machine-time bound.
Invalid references denote zero expressions; they are not uniformly rejected.

Replay that client independently:

```sh
lake build CSLibExtTest.Computability.Decidability.RegularExpressionRuntimeTests
lake env lean -DwarningAsError=true CSLibExtTest/Computability/Decidability/RegularExpressionRuntimeTests.lean
```

## Reproduce runtime coverage

For the three original clients, after building the corresponding targets with
`lake --wfail build`, these commands re-execute the assertions and print measured
corpus and branch counts:

```sh
lake env lean -DwarningAsError=true CSLibExtTest/Algorithms/Lean/DataStructures/BinaryHeapTests.lean
lake env lean -DwarningAsError=true CSLibExtTest/Computability/Languages/ContextFreeCYKTests.lean
lake env lean -DwarningAsError=true CSLibExtTest/Computability/CookLevinTests.lean
```
