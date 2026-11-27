# Conditional moment duality between the Λ-Wright–Fisher process and the Λ-coalescent

Let $\Lambda$ be a finite measure on $[0, 1]$ and, for integers $2 \le k \le n$, let $\lambda_{n,k} = \int_{[0,1]} y^{k-2} (1 - y)^{n-k}\, \Lambda(dy)$ be the rate at which a given $k$-tuple of $n$ blocks of the Λ-coalescent merges ([Pitman's merger rate](merger-rate.md)). The two-type Λ-Wright–Fisher generator acts on $f \in C^2[0, 1]$ by

$$\mathcal{L}^{\Lambda} f(x) = \frac{\Lambda(\{0\})}{2}\, x (1 - x) f''(x) + \int_{(0,1]} \bigl[x f(x + y(1 - x)) + (1 - x) f(x - y x) - f(x)\bigr]\, y^{-2}\, \Lambda(dy).$$

1. **Generator identity.** For every $n \ge 1$,

$$\mathcal{L}^{\Lambda} x^n = \sum_{k=2}^{n} \binom{n}{k} \lambda_{n,k} \bigl(x^{n-k+1} - x^n\bigr),$$

that is, $\mathcal{L}^{\Lambda}$ acts on the monomial $x^n$ as the [generator of the Λ-coalescent block-counting process](block-counting-generator.md) acts on the exponent $n$.

2. **Conditional duality.** Suppose $X$ is a $[0, 1]$-valued solution of the [martingale problem](../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md) for $\mathcal{L}^{\Lambda}$ on polynomials, started at $x \in [0, 1]$, and let $(N_t)$ be the block-counting process of the Λ-coalescent started from $n$ blocks. Then

$$\mathbb{E}_x\bigl[X_t^n\bigr] = \mathbb{E}_n\bigl[x^{N_t}\bigr], \qquad t \ge 0,\ n \ge 1,$$

so all solutions have the same one-dimensional marginals.

The statement assumes a solution; it does not assert that one exists. Existence is a separate construction, for example as a limit of Λ-Cannings models or from the [infinite lookdown construction](infinite-lookdown-de-finetti-limit-and-lambda-fl.md).

## Depends on

- [Martingale problems](../../../Probability/markov-chains/martingale-problems/martingale-problems-generic-definition.md)
- [Pitman's merger rate](merger-rate.md)
- [Generator of the Λ-coalescent block-counting process](block-counting-generator.md)

## Proof depends on

- [Pitman's consistency relation](merger-rate-consistent.md)

## Expansion

1. The generator identity, by expanding $x(x + y(1 - x))^n + (1 - x)(x(1 - y))^n - x^n$ in powers of $y$ and integrating against $y^{-2} \Lambda(dy)$, with the atom at $0$ giving the Kingman term. Check the identity symbolically for $n \le 4$ and for $\Lambda = \delta_0$, $\delta_1$ and the uniform measure.
2. The duality from the generator identity for any solution of the martingale problem, with the solution carried as a hypothesis.

## Sources

- A. Etheridge, *Some Mathematical Models from Population Genetics*, École d'Été de Probabilités de Saint-Flour XXXIX-2009, Lecture Notes in Mathematics 2012 (2011), <https://link.springer.com/book/10.1007/978-3-642-16632-7> (duality).
- J. Bertoin and J.-F. Le Gall, Stochastic flows associated to coalescent processes, *Probab. Theory Related Fields* 126 (2003) (flows of bridges; background).
- N. H. Barton, A. M. Etheridge and A. Véber, A new model for evolution in a spatial continuum (2010), <https://arxiv.org/abs/0904.0210> (duality discussion; background).
