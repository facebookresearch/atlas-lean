---
article_id: af_49e3185dd139b195a8ce5b98
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.multipleHarmonic
---

# Multiple Harmonic

Multiple harmonic sum `H_r^(n)` over `ZMod p`.

`H_r^(n)` is the sum over `0 < k_1 < ... < k_n ≤ r` of `1 / (k_1 * ... * k_n)`,
with `H_r^(0) = 1` and zero unless `0 ≤ n ≤ r`. Here strictly increasing
tuples are represented by `n`-element subsets of `Finset.Icc 1 r`, with
reciprocals as inverses in `ZMod p`. Both boundary cases are handled
automatically by `Finset.powersetCard`: the `0`-element powerset of any
finset is `{∅}` (empty product `1`), and out-of-range `n` gives `∅`
(empty sum `0`). Congruence modulo `p` is polynomial equality over
`ZMod p`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.MultipleHarmonic](../../../../sources/v2/MathlibExt.md)
- Mattarei–Tauraso, "Congruences of Multiple Sums Involving Sequences Invariant Under the Binomial Transform", J. Integer Sequences, stable URL `https://cs.uwaterloo.ca/journals/JIS/VOL13/Tauraso/tauraso22.tex`, Lemma `Gg`, semantic concept `jis_sem_1e299eb15a144f108cb2fe31`, statement `jis_9e5865a09e42b4fb025d838d`.
