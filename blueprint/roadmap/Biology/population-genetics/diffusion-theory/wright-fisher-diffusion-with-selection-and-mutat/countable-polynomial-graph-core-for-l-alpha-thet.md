# A countable polynomial core for the Wright–Fisher generator with selection and mutation

Fix $\alpha \in \mathbb{R}$ and $\theta_1, \theta_2 \ge 0$, and let $\mathcal{L}_{\alpha, \theta}$ be [the generator of the Wright–Fisher diffusion with selection and mutation](selection-mutation-generator.md). The set

$$\mathcal{G} = \bigl\{(p, \mathcal{L}_{\alpha, \theta}\, p) : p \text{ a polynomial with rational coefficients}\bigr\}$$

is a countable set of pairs of bounded continuous functions on $[0, 1]$ whose bounded-pointwise closure contains the graph $\{(f, \mathcal{L}_{\alpha, \theta} f) : f \in C^2[0, 1]\}$. So it satisfies the hypothesis of [a countable bounded-pointwise graph core](../../../../Probability/markov-chains/martingale-problems/countable-bounded-pointwise-graph-core-for-marti.md) for the Wright–Fisher martingale problem.

The proof: polynomials approximate $f$, $f'$ and $f''$ uniformly on $[0, 1]$, polynomials with rational coefficients approximate those in $C^2[0, 1]$, and $\mathcal{L}_{\alpha, \theta}$ is continuous from $C^2[0, 1]$ to $C[0, 1]$.

## Depends on

- [Countable bounded-pointwise graph core for martingale problems](../../../../Probability/markov-chains/martingale-problems/countable-bounded-pointwise-graph-core-for-marti.md)
- [Generator of the Wright–Fisher diffusion with selection and mutation](selection-mutation-generator.md)

## Expansion

1. The approximation of $f \in C^2[0, 1]$ by polynomials in the $C^2$ norm, then by polynomials with rational coefficients.
2. Uniform, hence bounded-pointwise, convergence of $\mathcal{L}_{\alpha, \theta}\, p_n$ to $\mathcal{L}_{\alpha, \theta} f$ when $p_n \to f$ in $C^2$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 4 (cores and martingale problems).
