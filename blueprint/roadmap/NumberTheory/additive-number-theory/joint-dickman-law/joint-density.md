# The joint Dickman law for consecutive integers

Let $P^+(n)$ be the largest prime factor for $n\ge2$. For every pair of real numbers $0<a,b<1$,

$$
\lim_{X\to+\infty}\frac{\#\{2\le n\le\lfloor X\rfloor:
 P^+(n)\le n^a,\ P^+(n+1)\le n^b\}}{X}=\rho(1/a)\rho(1/b),
$$

where $X$ is real and $\rho$ is the Dickman function, with $\rho(u)=1$ for $0\le u\le1$ and
$u\rho'(u)=-\rho(u-1)$ for $u>1$. Both thresholds use $n$ as their base. There is no logarithmic
weight. The source builds $\rho$ by starting with $h_0(u)=1$, iterating
$h_{j+1}(u)=1-\int_1^{\max(1,u)}h_j(t-1)/\max(1,t)\,dt$, and taking $h_{\lceil u\rceil}(u)$
on $u\ge0$.

## Depends on

- [Dickman characterization](../../../Analysis/special-functions/elementary-transcendental-functions/dickman-de-bruijn-function/is-dickman-de-bruijn.md)
- [Natural density](../natural-and-logarithmic-density/has-density.md)

## Expansion

Bridge the source finite-iteration construction to the unique continuous Dickman function on the nonnegative half-line; no value at negative input is used. Prove the simultaneous consecutive smooth-number count with the same cutoff base $n$ in both coordinates, with an error $o(X)$. A one-variable friable asymptotic does not prove independence.

## Sources

- [JointDickman.lean — `joint_law`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/JointDickman.lean#L43-L50)
