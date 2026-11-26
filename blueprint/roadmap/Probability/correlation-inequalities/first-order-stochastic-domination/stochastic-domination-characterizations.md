# Characterizations and closure properties of stochastic domination

Let $\mu, \nu$ be probability measures on a preordered measurable space $\alpha$.

1. $\nu \preceq_{\mathrm{st}} \mu$ iff $\int f\,d\nu \le \int f\,d\mu$ for every measurable monotone $f : \alpha \to [0,\infty]$, iff the same holds for every integrable measurable monotone $f : \alpha \to \mathbb{R}$.
2. On $\mathbb{N}$: $\nu \preceq_{\mathrm{st}} \mu$ iff $\nu([n, \infty)) \le \mu([n,\infty))$ for all $n$. On $\mathbb{R}$: iff the distribution functions satisfy $F_\mu(x) \le F_\nu(x)$ for all $x$. Mutual domination on $\mathbb{N}$ or $\mathbb{R}$ implies equality.
3. (Closure) Domination is preserved by monotone measurable maps; by mixtures, if $\nu \preceq_{\mathrm{st}} \mu$, the kernels satisfy $\eta(x) \preceq_{\mathrm{st}} \kappa(x)$ pointwise and $\kappa$ is monotone in $x$, then $\nu\eta \preceq_{\mathrm{st}} \mu\kappa$; by independent sums on ordered additive monoids; and $Y \le X$ almost surely under a coupling implies $\mathrm{law}(Y) \preceq_{\mathrm{st}} \mathrm{law}(X)$.

## Proof sketch

For a nonnegative monotone $f$, the layer-cake representation $\int f\,d\nu = \int_0^\infty \nu(\{f > s\})\,ds$ over the upper sets $\{f > s\}$ gives the inequality for nonnegative tests. For an integrable monotone real $f$, apply this to the nonnegative monotone functions $\max(f, -k) + k$; since $\mu$ and $\nu$ have the same total mass $1$, subtracting $k$ gives $\int \max(f,-k)\,d\nu \le \int \max(f,-k)\,d\mu$, and dominated convergence (by $|f|$) as $k \to \infty$ gives item 1. The converse takes $f = \mathbf 1_U$. Upper sets of $\mathbb{N}$ and $\mathbb{R}$ are rays, giving item 2. For mixtures, $\nu\eta(U) = \int \eta(x)(U)\,d\nu \le \int \kappa(x)(U)\,d\nu \le \int \kappa(x)(U)\,d\mu$ since $x \mapsto \kappa(x)(U)$ is monotone; sums are the special case of a translation kernel.

## Depends on

- [First-order stochastic domination](first-order-stochastic-domination.md)

## Proof depends on

- [Existence of a monotone coupling implies stochastic domination](../stochastic-domination-and-strassen-s-theorem/monotone-couplings-and-stochastic-domination/stochastically-dominated-of-exists-monot.md)

## Sources

- D. A. Levin and Y. Peres, "Markov Chains and Mixing Times", American Mathematical Society, 2nd ed., 2017.
- N. Alon and J. H. Spencer, "The Probabilistic Method", Wiley, 4th ed., 2016.
