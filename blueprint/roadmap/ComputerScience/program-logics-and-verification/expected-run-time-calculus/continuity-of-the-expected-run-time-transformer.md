# Continuity of the expected run-time transformer

For every program $C$ and every $\omega$-chain of [run-times](run-times.md) $f_1 \preceq f_2 \preceq \cdots$,

$$\mathrm{ert}[C](\sup_n f_n) = \sup_n \mathrm{ert}[C](f_n).$$

Consequently, for each guard $\xi$, body $C$ and run-time $f$ the map $X \mapsto \mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](X)$ is continuous, and by the Kleene fixed point theorem its least fixed point exists, so the [expected run-time transformer](expected-run-time-transformer.md) is well defined on loops.

## Depends on

- [Expected run-time transformer](expected-run-time-transformer.md)
- [Run-times](run-times.md)

## Proof depends on

- [Least fixed point of a Scott-continuous map](../../../Order/fixed-points-domain-theory/scott-continuous-maps-and-least-fixed-points/lfp.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 3, Lemma 1 (proof by induction on $C$ in Appendix A.6) and the paragraph after it; Appendix A.5 for the $\omega$-cpo structure.
