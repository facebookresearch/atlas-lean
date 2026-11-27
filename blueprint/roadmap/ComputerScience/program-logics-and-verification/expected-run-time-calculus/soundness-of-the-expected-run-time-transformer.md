# Soundness of the expected run-time transformer

For every program $C$, continuation [run-time](run-times.md) $f$ and state $\sigma$, the [expected run-time transformer](expected-run-time-transformer.md) equals the expected reward of reaching the sink in the [operational MDP](operational-markov-decision-process-of-a-probabilistic-program.md):

$$\mathrm{ExpRew}^{M^f_\sigma[\![C]\!]}(\langle \mathit{sink} \rangle) = \mathrm{ert}[C](f)(\sigma).$$

## Depends on

- [Expected run-time transformer](expected-run-time-transformer.md)
- [Operational Markov decision process of a probabilistic program](operational-markov-decision-process-of-a-probabilistic-program.md)
- [Run-times](run-times.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 4, Theorem 2 (proof by induction on $C$ in Appendix A.7).
