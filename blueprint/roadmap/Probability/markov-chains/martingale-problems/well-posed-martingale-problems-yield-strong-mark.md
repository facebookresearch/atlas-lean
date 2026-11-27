# Well-posed martingale problems give strong Markov families

Let $E$ be a Polish space and $A$ a set of pairs of bounded measurable functions on $E$ with a countable bounded-pointwise core $\{(f_k,g_k)\}$ whose $f_k$ are bounded continuous, as in [the countable core lemma](countable-bounded-pointwise-graph-core-for-marti.md). Suppose that for every $x\in E$ the $(A,\delta_x)$ [martingale problem](martingale-problems-generic-definition.md) has exactly one solution law $\mathbb P_x$ on $C([0,\infty),E)$, and that $x\mapsto\mathbb P_x(\Gamma)$ is measurable for every Borel set $\Gamma$ of path space. Let $Y$ be the coordinate process with its natural filtration $(\mathcal F_t)$. Then $(\mathbb P_x)_{x\in E}$ is a strong Markov family: for every $x$, every $\mathbb P_x$-almost surely finite $(\mathcal F_t)$-stopping time $\tau$ and every Borel set $\Gamma$ of path space,

$$\mathbb P_x\bigl((Y_{\tau+t})_{t\ge0}\in\Gamma\bigm|\mathcal F_\tau\bigr)=\mathbb P_{Y_\tau}(\Gamma)\qquad\mathbb P_x\text{-a.s.}$$

## Depends on

- [Regular conditional laws of a martingale-problem solution at a stopping time](regular-conditional-laws-of-a-martingale-problem.md)
- [Martingale problems](martingale-problems-generic-definition.md)
- [A countable bounded-pointwise core of the graph suffices for a martingale problem](countable-bounded-pointwise-graph-core-for-marti.md)

## Proof depends on

- [Uniqueness for martingale problems by duality](uniqueness-of-martingale-problems-by-duality.md)

## Expansion

A full proof page must establish:

- By the regular-conditional-law theorem, for $\mathbb P_x$-almost every $\omega$ the conditional law of the shifted path given $\mathcal F_\tau$ solves the $(A,\delta_{Y_\tau(\omega)})$ martingale problem; by uniqueness it equals $\mathbb P_{Y_\tau(\omega)}$.
- Measurability of $\omega\mapsto\mathbb P_{Y_\tau(\omega)}(\Gamma)$ from the measurability of $x\mapsto\mathbb P_x(\Gamma)$, so the right-hand side is a version of the conditional probability.
- The application recovering the strong Markov property of the Wright–Fisher diffusion with selection from uniqueness of its martingale problem, without first constructing its semigroup.

## Sources

- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Grundlehren 233, Springer (1979), <https://books.google.com/books?id=vKC1BwAAQBAJ> (strong Markov property from well-posedness).
- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley (1986), <https://onlinelibrary.wiley.com/doi/book/10.1002/9780470316658>, Ch. 4.
