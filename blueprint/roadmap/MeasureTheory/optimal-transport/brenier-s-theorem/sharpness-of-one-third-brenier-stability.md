# Three-atom sharpness of one-third Brenier stability

For every $d\ge2$, real $\alpha>1/3$ and $C>0$, put $Q=[-1,1]^d$ and let $\sigma$ be normalized Lebesgue measure on $Q$. There are distinct probability measures $\mu,\nu$ supported on $Q$, each consisting of exactly three distinct atoms in $Q$ with strictly positive weights totaling one, and Borel transports $T_\mu,T_\nu$ from $\sigma$ to the two targets. Each graph plan is the unique minimum-cost quadratic probability coupling for its respective source and target. In the quadratic Wasserstein metric the targets satisfy $0<W_2(\mu,\nu)$ and

$$C W_2(\mu,\nu)^\alpha < \left(\int\|T_\mu-T_\nu\|^2\,d\sigma\right)^{1/2}.$$

## Depends on

- [Wasserstein distance](../wasserstein-distances/wasserstein-distance/wasserstein.md), in the finite-cost quadratic specialization.

## Proof depends on

- [Brenier's theorem](brenier.md).
- Quantitative upper and lower bounds for a separating three-cell family: small target-to-target transport cost and large displacement on a source set of controlled volume.

## Expansion

Construct both triples, verify positive weights and optimal-cell assignments, then relate the family parameter to both distances and choose it for the requested $C,\alpha$. An endpoint instability alone would not establish the quantification over every $\alpha>1/3$.

## Sources

- OpenAI, [Brenier comparator, one_third_exponent_is_sharp](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Brenier.lean#L88-L103).
- OpenAI, [scope and accompanying papers](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/374.md).
