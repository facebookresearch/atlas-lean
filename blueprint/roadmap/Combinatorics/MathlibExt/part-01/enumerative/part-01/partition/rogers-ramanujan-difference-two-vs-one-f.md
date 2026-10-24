---
article_id: af_b7bc4e364afb628c626de783
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujanWanted.rogers_ramanujan_difference_two_vs_one_four
---

# Rogers Ramanujan

Rogers–Ramanujan identity (first form): for every `n`, the number of partitions
of `n` with pairwise gap at least two between distinct parts equals the number of
partitions of `n` all of whose parts are congruent to `1` or `4` modulo `5`.

The left side counts `p : Nat.Partition n` with `p.parts.Nodup` and
`a + 2 ≤ b` whenever `a < b` are parts of `p` (nodup forbids the repeated
equal parts that the gap condition alone would allow). The right side counts
`p : Nat.Partition n` with every part satisfying `m % 5 = 1 ∨ m % 5 = 4`.

Provenance: George E. Andrews and David Newman, "The Minimal Excludant in
Integer Partitions," Journal of Integer Sequences 23 (2020), Article 20.2.3,
quoted Rogers–Ramanujan theorem at lines 173–178.
Public TeX URL:
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Andrews/andrews5.tex`
Retrieved TeX SHA-256:
`9f5fc80c212b5dc9cb8d7bcbc905d717f1aa9673ad7ada690f3eca3065c308c9`

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gauss Binom](../../part-03/gaussian-binomial/gauss-binom.md)
- [Gauss Binom eq zero of lt](../../part-03/gaussian-binomial/gauss-binom-eq-zero-of-lt.md)
- [Gauss Binom mul q Poch Fin mul q Poch Fin](../../part-03/gaussian-binomial/gauss-binom-mul-q-poch-fin-mul-q-poch-fi.md)
- [Gauss Binom self](../../part-03/gaussian-binomial/gauss-binom-self.md)
- [Gauss Binom succ succ](../../part-03/gaussian-binomial/gauss-binom-succ-succ.md)
- [Gauss Binom zero right](../../part-03/gaussian-binomial/gauss-binom-zero-right.md)
- [Q Poch Fin](../../part-03/gaussian-binomial/q-poch-fin.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.Partition.RogersRamanujan](../../../../../../../sources/v2/MathlibExt.md)
