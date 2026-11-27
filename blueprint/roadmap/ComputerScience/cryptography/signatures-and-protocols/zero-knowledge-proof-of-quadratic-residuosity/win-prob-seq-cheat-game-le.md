# Soundness error $2^{-m}$ over $m$ rounds

If $y$ is not a square, every adaptive cheating prover passes all $m$ rounds of the
[quadratic-residuosity protocol](sigma.md) with probability at most $2^{-m}$.

## Informally uses

- [Soundness error of sequential repetition](../zero-knowledge-proofs/soundness-error-of-sequential-repetition.md)
- [Special soundness of the quadratic-residuosity protocol](sigma-special-sound.md)

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, Claim 1 ("the probability that $B$ will say 'convinced' is at most $1/2^m$").
