# Continuity of the expected run-time transformer

For every program $C$ and every $\omega$-chain of [run-times](run-times.md) $f_1 \preceq f_2 \preceq \cdots$,

$$\mathrm{ert}[C](\sup_n f_n) = \sup_n \mathrm{ert}[C](f_n).$$

Consequently, for each guard $\xi$, body $C$ and run-time $f$ the map $X \mapsto \mathbf{1} + [\![\xi : \mathrm{false}]\!] \cdot f + [\![\xi : \mathrm{true}]\!] \cdot \mathrm{ert}[C](X)$ is continuous, and by the Kleene fixed point theorem its least fixed point exists, so the [expected run-time transformer](expected-run-time-transformer.md) is well defined on loops.

## Depends on

- [Expected run-time transformer](expected-run-time-transformer.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *ESOP 2016*, LNCS 9632, Springer, 2016; extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, Section 3, Lemma 1 (proof by induction on $C$ in Appendix A.6) and the paragraph after it; Appendix A.5 for the $\omega$-cpo structure.
