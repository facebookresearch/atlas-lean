# Finite-entropy dyadic regularization with expected depth and attempts

Use the dyadic cells of the [uniform-cube model](models/dyadic-cell-localization-model.md). Fix a cell $Q$ and a probability $P$ absolutely continuous with respect to its uniform law $U_Q$ with finite KL. To regularize a conditional law in a current cell, call a proper descendant at depth increment $h>0$ heavy if its mass exceeds $2^{-nh/2}$, and select the first heavy descendants (no strictly intermediate heavy ancestor). Record the selected cell if the signal falls in one; otherwise record the residual symbol. Update the conditioning event by intersecting with the chosen cell or residual and keep the same current cell for the residual symbol. Stop after a residual step if its conditional mass before this step is at least $1/2$. Begin with event $Q$ and current cell $Q$.

For all sufficiently large $n$, the process stops $P$-almost surely and the finite terminal log (with the source's empty default on nontermination) is measurable. For every positive-mass terminal log $h$, the associated terminal cell $Q_h$ is a descendant of $Q$ and the law $P_h$ conditional on that log is supported in $Q_h$ and gives each proper descendant at level increment $j$ mass at most $2\,2^{-nj/2}$. Let $D$ be the terminal level minus the initial level and $A$ the number of attempts. Both are integrable, with $\mathbb E A\le2(1+\mathbb E D)$, and

$$
\mathbb E\,D_{\rm KL}(P_h\|U_{Q_h})+\frac{n\log2}{4}\,\mathbb E D\ \le\ D_{\rm KL}(P\|U_Q)+2/e,
$$

where the first expectation is an extended nonnegative integral over the realized terminal log.

**Conventions.** Use nested dyadic boxes with countable levels, heavy and first-heavy cells for the current conditional law, the transcript probability of each branch, and KL relative to uniform cell laws.

First-heavy cells are disjoint by minimality, so their selected cell is unique if there is one.

## Depends on

- [Dyadic cell disclosures and Gaussian block localization](models/dyadic-cell-localization-model.md)


## Proof depends on

A conditional entropy budget for the first-heavy tree and control of residual attempts, followed by stopping and terminal conditional law estimates for finite entropy.

## Expansion

Establish measurability of the finite-stage and terminal logs, and estimate finite truncations before passing to the terminal process. Separate heavy advances from repeated residual attempts, account for the KL fee of the disclosure and the $2/e$ remainder, and prove the terminal regularity on positive-mass logs only.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianFiniteEntropy.lean#L198-L200)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Localization costs and information growth for exact Gaussian observations](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf)
