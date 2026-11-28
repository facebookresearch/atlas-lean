# Characterization of trade-off functions

A function $f : [0,1] \to [0,1]$ is the trade-off function $T(P,Q)$ of some pair of distributions if and only if $f$ is convex, continuous, nonincreasing, and satisfies $f(\alpha) \le 1 - \alpha$ for all $\alpha \in [0,1]$. Moreover, every such $f$ is the trade-off function of a pair of distributions on $[0,1]$, and $T(P,Q) \ge T(P', Q')$ whenever $(P,Q)$ is a post-processing of $(P', Q')$ by a common Markov kernel.

## Proof sketch

Convexity follows by randomizing between two rejection rules, monotonicity and continuity from the definition as an infimum over a convex compact set of $(\alpha_\phi, \beta_\phi)$ pairs, and $f(\alpha) \le 1-\alpha$ from the trivial rule $\phi \equiv \alpha$. Conversely, given such $f$, take $P$ uniform on $[0,1]$ and let $Q$ be the distribution on $[0,1]$ with distribution function $F_Q(x) = f(1 - x)$, completed by an atom at $1$ if needed; tests rejecting for large $x$ are Neyman–Pearson optimal and reproduce $f$. Post-processing can only shrink the set of achievable error pairs, since any test on the processed outputs is a test on the originals.

## Depends on

- [Trade-off functions of pairs of distributions](trade-off-function.md)

## Proof depends on

- [Neyman–Pearson lemma](../../../../Probability/hypothesis-testing/neyman-pearson-dominated-two-simple.md)

## Sources

- J. Dong, A. Roth, W. J. Su, "Gaussian Differential Privacy", Journal of the Royal Statistical Society Series B 84 (2022), arXiv:1905.02383.
