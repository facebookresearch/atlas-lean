# Omega-invariants

Let $f$ be a [run-time](run-times.md), $C$ a program, $\xi$ a probabilistic guard, $F = F^{\langle \xi, C \rangle}_f$ the [characteristic functional](characteristic-functional-of-a-loop.md) of $\mathbf{while}\ (\xi)\ \{C\}$, and $(I_n)_{n \in \mathbb{N}}$ a family of run-times. $(I_n)$ is a *lower $\omega$-invariant* of the loop with respect to $f$ if

$$I_0 \preceq F(\mathbf{0}) \qquad\text{and}\qquad I_{n+1} \preceq F(I_n) \text{ for all } n \ge 0,$$

and an *upper $\omega$-invariant* if $F(\mathbf{0}) \preceq I_0$ and $F(I_n) \preceq I_{n+1}$ for all $n \ge 0$.

## Depends on

- [Characteristic functional of a loop](characteristic-functional-of-a-loop.md)
- [Run-times](run-times.md)

## Sources

- B. L. Kaminski, J.-P. Katoen, C. Matheja and F. Olmedo, "Weakest precondition reasoning for expected run-times of probabilistic programs", *Programming Languages and Systems (ESOP 2016)*, LNCS 9632, Springer, 2016, pp. 364–389, <https://doi.org/10.1007/978-3-662-49498-1_15>, author copy <https://users.dcc.uchile.cl/~folmedo/pubs/2016.ESOP.pdf>, with the same numbering as the extended version arXiv:1601.01001v2, <https://arxiv.org/abs/1601.01001v2>, whose appendices contain the proofs, Section 5.2, Definition 4.
