# Levene's formula is the conditional law under random union of gametes

Among the
`C(2N, nA)` equally likely placements of the `nA` copies of `A` in the `2N` gamete slots, the
fraction with exactly `h` heterozygous individuals is `leveneProb N nA h`.

No hypothesis `nA ≤ 2N` is needed: for `nA > 2N` there is no placement and `C(2N, nA) = 0`, so
the left side is `0 / 0 = 0`, matching `leveneProb N nA h = 0`; the statement is meaningful for
`nA ≤ 2N`. The uniform law on placements is taken as the model; deriving it from independent
gametes conditioned on `nA` is not part of this file.

## Sources

- Levene (1949); Wigginton, Cutler and Abecasis (2005).
