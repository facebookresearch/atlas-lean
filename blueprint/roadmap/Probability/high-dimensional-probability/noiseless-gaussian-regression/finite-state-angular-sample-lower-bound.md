# A finite-state sample lower bound for noiseless Gaussian angular regression

An unknown unit signal $s\in\mathbb R^d$ is observed through $T$ independent pairs $(X_j,\langle X_j,s\rangle)$ with $X_j\sim N(0,I_d)$. A randomized learner has an independent seed and at most $2^M$ memory states between observations. It may stop before any samples or at any step through $T$. The initial choice, transition and stopping bit, and unit-vector output are functions respectively of the seed, the seed/time/state/current observation, and the seed/terminal time/state. The admissibility conditions are almost-everywhere measurability for the initial and output maps under the seed law, the transition at each time/state under seed times Gaussian-row times Lebesgue-label reference, and the entire output for each fixed-signal and uniform-sphere product experiment. Success is probability of angle $\arccos\langle\widehat s,s\rangle\le\varepsilon$; the seed and rows are independent of the signal in the uniform experiment.

There is an absolute $c>0$ such that for every memory sequence $M(d)=o(d^2)$, all sufficiently large $d$, all $T$, and all $0<\varepsilon\le1/10$, success at least $2/3$ under the uniform sphere prior **or** separately for every fixed signal implies $T\ge c d\log(1/\varepsilon)$. Also, for each fixed $A_0>0$ there are $c>0,d_0$ such that the same lower bound follows for $d\ge d_0$ and $M\le A_0d^2$ from success at least $2/3$ under the uniform prior. The latter constant may depend on $A_0$.

**Conventions.** Use the explicit finite-state, seeded, possibly early-stopping learner and measurable angular loss, with all observations noiseless and the seed independent. The label reference law for measurability is not the actual observation law.

## Depends on

- [Seeded finite-state noiseless Gaussian learner](seeded-noiseless-gaussian-learner.md)

## Proof depends on

Finite-state information control at both memory scales, the angular small-ball estimate under the sphere prior, and a stopping-to-budget transfer that does not require storing the full history.

## Expansion

Keep the $2/3$ threshold in the extended nonnegative real type; the quotient is not natural-number division.

Build the shared learner semantics, including stopping at zero and a possibly time-dependent terminal output. Compare observation block gains to the information needed for angular accuracy, and separate universal subquadratic constants from the fixed quadratic coefficient. Do not lower the stated success threshold or infer average-to-worst guarantees in the wrong direction.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NoiselessRegression.lean#L118-L120)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Memory and precision in noiseless Gaussian regression](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Memory-and-precision-in-noiseless-Gaussian-regression-September-27-2026/paper.pdf)
- [Pinned experiment definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/NoiselessRegression.lean#L71-L96)
