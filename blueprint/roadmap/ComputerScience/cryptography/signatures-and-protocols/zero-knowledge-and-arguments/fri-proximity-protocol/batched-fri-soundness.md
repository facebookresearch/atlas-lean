# Soundness of batched FRI

In batched FRI a list of words $f_1, \dots, f_t$ on $D_0$ is combined with verifier randomness into one word before folding. Say the batch is $e$-far if no common set of $2^d - e$ positions carries codewords for all $f_j$ (failure of correlated agreement; for $0 < \alpha \le 1$ this is the same as being outside the $\alpha$-correlated-agreement language with $e = 2^d - \lceil \alpha 2^d\rceil$). Then the probability that the batched word is $e$-close to the code, i.e. the round-$0$ escape, is bounded by the affine (or curve) proximity-gap bound, $(t - 1)\,2^d/|\mathbb{F}|$ in the unique-decoding regime and a Johnson-regime bound up to $e/2^d \le 1 - \sqrt\rho - \sqrt\rho/(2m)$; the subsequent rounds are bounded as for single-word FRI. Hence interactive batched FRI is sound with error at most the round-$0$ batching term plus the FRI error, and its BCS compilation satisfies the BCS bound with the round-$0$ batching term as one more round error.

## Proof sketch

Random linear combinations of a batch without correlated agreement are far from the code except with the proximity-gap probability; from then on the single-word analysis applies.

## Depends on

- [The FRI protocol](fri-protocol.md)

## Proof depends on

- [Proximity gaps and correlated agreement for Reed–Solomon codes](reed-solomon-proximity-gaps.md)
- [Round-by-round soundness of FRI](fri-round-by-round-soundness.md)
- [Soundness and straight-line knowledge soundness of the BCS transform](../interactive-oracle-proofs/bcs-soundness.md)

## Sources

- Eli Ben-Sasson et al., "Proximity Gaps for Reed–Solomon Codes", Journal of the ACM, 2023.
