---
article_id: af_49a60222284429c26a081878
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniformWanted.brun_titchmarsh_uniform
---

# Brun Titchmarsh Uniform

For every exponent `β ∈ (0, 1)` there is a constant `ξ₁ > 0`, depending only
on `β`, such that the inclusive residue-class prime count satisfies
`π(X; k, ell) < ξ₁ X / (φ(k) log(X/k))` whenever `2 ≤ X`, `1 ≤ k`, and
`k ≤ X ^ β`.

Proof: Selberg's `Λ²` upper-bound sieve on an arithmetic progression, with
optimized weights and a harmonic lower bound for the diagonal sum.

## Depends on

- [Prime Counting Mod](../part-02/residue-class/prime-counting-mod.md)

## Proof depends on

- [Level Set](../../../part-10/selberg-sieve/level-set.md)
- [Level Sum](../../../part-10/selberg-sieve/level-sum.md)
- [Level Weights](../../../part-10/selberg-sieve/level-weights.md)
- [Level Weights err Sum le](../../../part-10/selberg-sieve/level-weights-err-sum-le.md)
- [Level Weights main Sum](../../../part-10/selberg-sieve/level-weights-main-sum.md)
- [Level Weights one](../../../part-10/selberg-sieve/level-weights-one.md)
- [Prime Counting Mod eq card filter range](../part-02/residue-class/prime-counting-mod-eq-card-filter-range.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.PrimeCounting.BrunTitchmarshUniform](../../../../../../sources/v2/MathlibExt.md)
- Jean-Marie De Koninck and Imre Kátai, "Some Remarks on a Paper of L. Toth," Journal of Integer Sequences 13 (2010), `https://cs.uwaterloo.ca/journals/JIS/VOL13/DeKoninck/dekoninck7.tex`, Lemma `lem:pi`, lines 424–429. Both the live and bundled source have SHA-256 `a81e23b6e88f02c8bcad5f1b6e4d71d822e82e1725a9e8ba2708bd2bc0e4a57d`, and the exact lines 424–429 joined by LF without a terminal LF have SHA-256 `bd645263ac19a24bf1b4ff3ac5baf13ec5ee8f59ae16945edd528cf4ac153828`. The source cites E. C. Titchmarsh, "A divisor problem," Rend. Palermo 54 (1930), 414–429 and 57 (1933), 478–479. The bound `2 ≤ X` makes the source's implicit analytic lower range explicit, and the source prints no coprimality hypothesis.
