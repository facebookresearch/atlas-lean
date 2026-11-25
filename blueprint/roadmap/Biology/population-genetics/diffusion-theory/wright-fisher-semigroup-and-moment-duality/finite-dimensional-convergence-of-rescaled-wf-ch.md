# Finite-dimensional convergence of rescaled neutral Wright–Fisher chains

Let $P_t$ be [the neutral Wright–Fisher diffusion semigroup](wf-semigroup.md), and suppose that the rescaled one-generation operators converge uniformly, $(\text{one Wright–Fisher generation on } M \text{ copies})^{\lfloor tM \rfloor} f \to P_t f$ for $f \in C[0, 1]$, as in [the diffusion approximation of the transition operators](tendsto-wf-step-pow-floor.md). Let $X^{(M)}$ be the neutral Wright–Fisher frequency chain on $M$ gene copies started at $x_M \to x$, and $0 \le t_1 < \cdots < t_k$. Then the laws of

$$\bigl(X^{(M)}_{\lfloor t_1 M \rfloor}, \dots, X^{(M)}_{\lfloor t_k M \rfloor}\bigr)$$

converge weakly to the finite-dimensional distribution of the neutral Wright–Fisher diffusion started at $x$ at times $t_1, \dots, t_k$.

## Depends on

- [Neutral Wright–Fisher diffusion semigroup](wf-semigroup.md)
- [Diffusion approximation of the Wright–Fisher transition operators](tendsto-wf-step-pow-floor.md)
- [Path-space measure of a Markov semigroup](../../../../Probability/markov-chains/markov-processes-from-transition-semigroups/path-measure.md)

## Proof depends on

- [Neutral Wright–Fisher transition matrix](../../wright-fisher-markov-chain/wright-fisher.md)
- [Stone–Weierstrass theorem for star subalgebras](../../../../Topology/function-spaces/stone-weierstrass-star-subalgebra.md)

## Expansion

1. Induction on $k$ with the Markov property, using the uniform convergence of the operators and the Feller continuity of $P_t$ in $x$.
2. The case $k = 1$ is [the diffusion approximation of the transition operators](tendsto-wf-step-pow-floor.md) together with the Feller continuity in $x$.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://doi.org/10.1002/9780470316658>, Chapter 1, Section 6, Chapter 4, Section 2, and Chapter 10, Theorem 1.1.
