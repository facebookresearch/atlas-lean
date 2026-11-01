---
article_id: af_4b5afed2126563490f1e8403
declaration: theorem
origin: cited
statement: formalized
lean: MathlibExt.Algebra.AbelRuffiniWanted.abel_ruffini
---

# Abel–Ruffini theorem

**Abel–Ruffini theorem** (§57). For each positive `n`, every root in `ℂ` of
every nonzero rational polynomial of degree `n` lies in `solvableByRad ℚ ℂ` iff
`n ≤ 4`. The forward direction (universal radical solvability implies
`n ≤ 4`) is the classical insolvability of the general quintic, padded to
higher degrees; the reverse direction proves radical solvability for
degrees at most four using the explicit low-degree (Cardano/Ferrari)
formulas. This corrects the direction descriptions in the lean-eval
source docstring, which assigned the two arguments to the opposite
implications.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Algebra.AbelRuffiniWanted](../../../sources/v2/WantedExt.md)
- P. Ruffini (1799), N. H. Abel (1824), É. Galois (1832). Listed as §57 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf); the general-quintic insolvability is #16 on Freek Wiedijk's *Formalizing 100 Theorems* list (https://www.cs.ru.nl/~freek/100/). Taken verbatim, with no Lean variant, from leanprover/lean-eval at commit 38361be884302c7edce1908c4aef8296eb2cb27e, manifest `manifests/problems/abel_ruffini.toml` (statement revision 1), module `LeanEval.Algebra.AbelRuffini`, hole `abel_ruffini`.
