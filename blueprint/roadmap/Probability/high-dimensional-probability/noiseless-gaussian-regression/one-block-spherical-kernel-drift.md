# Spherical kernel-potential drift for actual Gaussian rows

Let $\mu$ be any joint probability of a signal $S$ and a state in $[N]$, with signal marginal $\sigma_d$ as in the [spherical potential model](models/gaussian-block-spherical-potential.md). At state $v$ draw a fresh independent block of $k=\lfloor d/16\rfloor$ standard Gaussian rows, form their exact inner products with $S$, and use any measurable nonnegative normalized transition probabilities for an outgoing state $w\in[N]$ from $(v,\text{rows},\text{labels})$. Denote the resulting joint law of $(S,w)$ by $\mu'$. For each law, take its signal posterior at each state by restricting to that state then dividing by its mass. Put $\overline F(\mu)=\sum_v P(v)F(P(S\in\cdot\mid v))$, with zero-mass states contributing zero.

There exist $C>0,d_0$ so that for $d\ge d_0$, $N\ge1$, and $\log N\le d^2$, one has $\overline F(\mu')\le\overline F(\mu)+Cd$ for every such law and rule.

**Conventions.** Use the exact row/label joint law (not disclosure of state alone), finite-state posteriors and the [spherical potential](models/gaussian-block-spherical-potential.md).

## Depends on

- [Spherical kernel potential and outgoing posterior laws](models/gaussian-block-spherical-potential.md)


## Expansion

Isolate a uniform comparison of the old and updated, label-conditioned Riesz potentials under actual Gaussian rows. Prove the positive-mass posterior domination with the correct rescaling, then use the comparison to control the potential change with $\log N\le d^2$. Do not replace the actual row-label coupling by independent labels.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L201-L201)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/140.md)
- [Accompanying manuscript: Localization costs and information growth for exact Gaussian observations](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Localization-costs-and-information-growth-for-exact-Gaussian-observations-September-27-2026/paper.pdf)
