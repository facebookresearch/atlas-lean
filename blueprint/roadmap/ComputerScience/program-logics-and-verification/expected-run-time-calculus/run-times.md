# Run-times

A *run-time* is a function $f : \Sigma \to \mathbb{R}^\infty_{\ge 0}$ from program states to the nonnegative reals extended with $\infty$; let $\mathbb{T}$ be the set of run-times, ordered pointwise by $f \preceq g \iff f(\sigma) \le g(\sigma)$ for all $\sigma$. $(\mathbb{T}, \preceq)$ is an $\omega$-complete partial order with bottom element $\mathbf{0} = \lambda\sigma.\, 0$, in which the supremum of an $\omega$-chain $f_1 \preceq f_2 \preceq \cdots$ is taken pointwise, $\sup_n f_n = \lambda\sigma.\, \sup_n f_n(\sigma)$. Constants, sums, scalar multiples, pointwise maxima and products with $[0, 1]$-valued functions of states are taken pointwise.

## Depends on

- [Probabilistic programs with a run-time model](probabilistic-programs-with-a-run-time-model.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 3 (the space $\mathbb{T}$ and the remark on well-definedness).
