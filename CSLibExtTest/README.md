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
| [`cykAccepts` / `cykAccepts_iff`](../CSLibExt/Computability/Languages/ContextFree/CYK.lean#L382), with full Chomsky-normal-form hypotheses | [ContextFreeCYKTests](Computability/Languages/ContextFreeCYKTests.lean): 10 fixed + 511 exhaustive + 1,000 generated words per `anbn`/`epsAB`; one shared generated corpus, length ≤ 12, seed 2026110402; 10 singleton/empty-rule boundary checks | [Commands below](#reproduce-runtime-coverage) |
| [`decodeCNF` / `decodeCNF_eq_some_iff`](../CSLibExt/Computability/CookLevin.lean#L108): entire input equals the returned formula's encoding | [CookLevinTests](Computability/CookLevinTests.lean): 1,000 generated formulas (≤ 3 clauses, ≤ 4 literals/clause, indices 0..7, seed 2026110404), 4,227 checks including fixed/raw encodings, ordered duplicates, truncations and nonempty suffixes; reuses [tokenizer name guards](Computability/Complexity/SatTokenizerTests.lean#L79) | [Commands below](#reproduce-runtime-coverage) |

## Reproduce runtime coverage

After building the corresponding targets with `lake --wfail build`, these commands
re-execute the assertions and print measured corpus and branch counts:

```sh
lake env lean -DwarningAsError=true CSLibExtTest/Algorithms/Lean/DataStructures/BinaryHeapTests.lean
lake env lean -DwarningAsError=true CSLibExtTest/Computability/Languages/ContextFreeCYKTests.lean
lake env lean -DwarningAsError=true CSLibExtTest/Computability/CookLevinTests.lean
```
