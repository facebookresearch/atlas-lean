# Finite strongly Rayleigh response and a uniform Lipschitz bound

For a finite nonempty set $F$, let $\mu$ be a probability law on $\{0,1\}^F$ with generating polynomial $G(z)=\sum_x\mu(x)\prod_{i:x_i=1}z_i$ nonzero whenever every $\operatorname{Im}z_i>0$ (the strongly Rayleigh property). Given $h\in\mathbb R^F$, tilt by the positive weights $\exp(\sum_j h_jx_j)$ and normalize. Let $m_i(h)$ and $C_{ij}(h)$ be the mean of $X_i$ and covariance of $(X_i,X_j)$ in the tilted law. Then for every $h,i,j$,

$$
\left.\frac{d}{dr}m_i(h+re_j)\right|_{r=0}=C_{ij}(h),\qquad
\sum_j|C_{ij}(h)|\le2m_i(h)(1-m_i(h))\le\tfrac12.
$$

For every $h,h',i$ and $D\ge0$ such that $|h_j-h'_j|\le D$ for all $j$, one has $|m_i(h)-m_i(h')|\le D/2$.

**Conventions.** Use real stability of the multiaffine probability generating polynomial and the finite tilted law, with positive partition function and Bernoulli-coordinate covariance.

## Depends on

- [Strongly Rayleigh generating polynomials and determinantal cylinder laws](binary-law-generating-models.md)

## Expansion

Stability under positive external fields and a stochastic-covering or equivalent conditional comparison strong enough to bound the sum of the absolute off-diagonal covariances by the variance of coordinate $i$.

Differentiate the finite tilted quotient, use the two conditional laws given $X_i=0,1$ to control the total off-diagonal response, and integrate along the straight line from $h$ to $h'$. Handle deterministic $X_i$ without dividing by a zero conditioning probability.

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/StronglyRayleighDPP.lean#L132-L146)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/231.md)
- [Accompanying manuscript: The free uniform spanning forest is a factor of IID](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026/The-free-uniform-spanning-forest-is-a-factor-of-IID-September-25-2026.pdf)
