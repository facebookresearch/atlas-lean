# Telescoped mirror-prox bound

In the setting of the [ergodic rate](mirror-prox-average-le.md), without assuming monotonicity: if $0 < \gamma$, $\gamma L \le \alpha$ and $F$ is $L$-Lipschitz on $Z$, then the leading points satisfy, for every $u \in Z$ and every $N$,

$$
\gamma \sum_{t<N} F(w_t)(w_t - u) \le V_{z_0}(u) .
$$

It is the sum of the [one-step inequality](mirror-prox-step-le.md). Monotonicity turns it into the variational-inequality bound; convexity-concavity turns it into the [saddle-point bound](mirror-prox-saddle-le.md).

## Sources

- A. Nemirovski, *Prox-method with rate of convergence O(1/t) for variational inequalities with Lipschitz continuous monotone operators and smooth convex-concave saddle point problems*, SIAM J. Optim. 15(1) (2004), 229–251; author PDF at <https://www2.isye.gatech.edu/~nemirovs/SIOPT_042562-1.pdf>, Section 3, Lemma 3.1, summed over the steps as in the proof of Proposition 2.2.
