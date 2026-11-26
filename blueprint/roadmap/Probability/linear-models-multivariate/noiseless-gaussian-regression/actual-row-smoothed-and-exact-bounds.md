# Smoothed and exact Gaussian density bounds with actual rows

Let $d,m,r,q$ be natural numbers with $m,r,q\ge1$, $m+r<d-1$ and $r\ge q$. On the unit sphere take a joint probability $P$ of $(S,W,X)$ with $W$ countable and singletons measurable and $X$ an array of $m$ real rows. The $(S,X)$ law is $\nu\otimes\gamma_m$ for Gaussian row law $\gamma_m$ and a probability $\nu$ dominated by $\max(H,0)\sigma_d$ for some real $H$. Let $H(W)<\infty$ be the countable Shannon entropy in nats. For every positive-mass message $w$, take a finite $\rho_w\ll\sigma_d$ and constants $B_w,D_w>0$ such that every closed ball of radius $t>0$ centered in the ambient Euclidean space has $\rho_w$-mass at most $B_wt^{m+r}$ and at most $D_wt^{d-1}$. Extend these families at zero-mass messages by $\rho_w=0$, $B_w=D_w=1$. Suppose $g(w)=\log(1+e^{9d}B_w(1+\max(0,\log(D_w/B_w))))$ is integrable in the signal-message marginal.

Adjoin $r$ independent fresh Gaussian rows $Z$ and set $G=(X,Z)$, $Y=GS$. Write $A_\delta=D_\delta(\rho_W;G,Y)$ and $A_0=D_0(\rho_W;G,Y)$. With $I=\operatorname{KL}(P\|P_{S,W}\otimes\gamma_m)$, the conclusions are:

* $I$ is finite, $I\le H(W)$, and the conditional law of $Y$ given $(G,W)$ is absolutely continuous with respect to volume almost everywhere.
* $A_{1/j}\to A_0$ almost surely. For every $\delta>0$ and for the exact value $A_0$, the quantity $\log(1+A_\delta)$ (using the real projection of $A_\delta$) is integrable and its mean is at most $I/q+\mathbb E g(W)\le H(W)/q+\mathbb E g(W)$.
* The positive log part of $A_0$ is integrable and its extended log expectation is at most $I/q+\mathbb E g(W)$. For this expectation the negative part at zero is $+\infty$ before subtraction; elsewhere use the positive and negative parts of the log of the real projection.

**Conventions.** Use the conditional label law with the actual $(S,W,X)$ correlation, a countable-message entropy, and the mixed projection density model for each positive-mass message.

## Depends on

- [Noiseless Gaussian row and label density models](gaussian-projection-density-model.md)

## Proof depends on

- [The mixed projection moment estimate](mixed-projection-density-moments.md)

Use a KL comparison between actual rows and fresh independent rows and pass from projection limits to the exact random density.

## Expansion

Separate the KL/entropy bound, conditional absolute continuity, moment-based logarithmic estimate, exact-density limit and extended-log estimate. Do not assume that the selected measure $\rho_w$ is the actual posterior; it is arbitrary under the displayed hypotheses.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L436-L456)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Replacing Gaussian observations in memory-constrained inference](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Replacing-Gaussian-observations-in-memory-constrained-inference-September-27-2026/paper.pdf)
- [Pinned model and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianReplacement.lean#L12-L94)
