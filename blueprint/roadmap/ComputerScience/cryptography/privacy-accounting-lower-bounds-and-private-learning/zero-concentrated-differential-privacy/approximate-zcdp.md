# Approximate zero-concentrated differential privacy

For $\rho \ge 0$ and $0 \le \delta < 1$, a mechanism $M$ is **$\delta$-approximately $\rho$-zCDP** if for every pair of neighbouring datasets $S, S'$ there exist events $E$ and $E'$, defined on the randomness of the runs $M(S)$ and $M(S')$ respectively (they may depend on the mechanism's internal coins, not only on its output), with $\Pr[E] \ge 1 - \delta$ and $\Pr[E'] \ge 1 - \delta$ (positive, since $\delta < 1$, so the conditional laws are defined), such that both conditional Rényi bounds hold for this same pair of events:

$$
D_\alpha\big(M(S) \mid E \,\big\|\, M(S') \mid E'\big) \le \rho\alpha \quad\text{and}\quad D_\alpha\big(M(S') \mid E' \,\big\|\, M(S) \mid E\big) \le \rho\alpha \qquad \text{for all } \alpha \in (1, \infty).
$$

Requiring the two directions separately, each with its own choice of events, would be weaker, since reversing the ordered pair after choosing events may choose different events. With $\delta = 0$ this is $\rho$-zCDP. If $M$ is $\delta$-approximately $\rho$-zCDP and, for every output $y$ of $M$, $M'(\cdot, y)$ is $\delta'$-approximately $\rho'$-zCDP, with $0 \le \delta, \delta' < 1$, then the adaptive composition is $(\delta + \delta' - \delta\delta')$-approximately $(\rho + \rho')$-zCDP, and post-processing preserves the guarantee. The definition unifies approximate differential privacy with concentrated privacy: every $(\varepsilon,\delta)$-differentially private mechanism with $\delta < 1$ is $\delta$-approximately $\tfrac12\varepsilon^2$-zCDP.

## Proof sketch

For the unification, fix neighbours $x_0, x_1$; an $(\varepsilon,\delta)$-differentially private mechanism on this pair is a post-processing of a canonical randomized-response mechanism that, with probability $\delta$, reveals which input it was given and otherwise acts as $\varepsilon$-DP binary randomized response. Taking $E_b$ to be the event that the canonical mechanism does not reveal its input, which has probability $1 - \delta$ and is an event of the mechanism's internal randomness, the conditional laws are post-processings of an $\varepsilon$-DP pair, so their Rényi divergences in both directions are at most $\tfrac12\varepsilon^2\alpha$. For composition, fix neighbours, events $E, E'$ for the first stage and, for each first output $y$, events $F_y, F'_y$ for the second. Intersecting directly would reweight the first output, since the conditional probability of $F_y$ may depend on $y$. So first thin the second-stage events with independent auxiliary coins to conditional probability exactly $1 - \delta'$ for every $y$; this does not change the conditional laws given them. Conditioning on $E \cap F_Y$ then leaves the law of the first output $Y$ equal to its law given $E$, and given $Y = y$ the second output has its law given $F_y$; so the conditional joint law is the adaptive composition of the conditional laws, the zCDP composition rule bounds its Rényi divergences in both directions by $(\rho + \rho')\alpha$, and the intersection has probability at least $(1-\delta)(1-\delta') = 1 - (\delta + \delta' - \delta\delta')$.

## Depends on

- [Zero-concentrated differential privacy](zero-concentrated-dp.md)
- [Differential privacy](../../differential-privacy/differentially-private.md)

## Proof depends on

- [Adaptive composition and post-processing of zCDP](zcdp-composition-and-post-processing.md)
- [Pure differential privacy implies zCDP with half the squared parameter](pure-dp-implies-zcdp.md)

## Sources

- M. Bun, T. Steinke, "Concentrated Differential Privacy: Simplifications, Extensions, and Lower Bounds", TCC (2016), arXiv:1605.02065, Definitions 1.12 and 8.1, Proposition 1.13, Lemma 8.2 and Corollary 8.7.
