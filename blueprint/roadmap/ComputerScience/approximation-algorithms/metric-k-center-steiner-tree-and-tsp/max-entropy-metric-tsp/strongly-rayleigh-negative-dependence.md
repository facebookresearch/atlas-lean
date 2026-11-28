# Negative dependence and Poisson-binomial counts under strongly Rayleigh measures

Let $\mu$ be strongly Rayleigh on $2^{[m]}$ and $S \sim \mu$.

(i) For distinct $i,j$: $\mathbb{P}[i \in S, j \in S] \le \mathbb{P}[i \in S]\,\mathbb{P}[j \in S]$.

(ii) (Negative association) For increasing functions $f,g:2^{[m]} \to \mathbb{R}$ depending on disjoint sets of coordinates, $\mathbb{E}[f(S)g(S)] \le \mathbb{E}[f(S)]\,\mathbb{E}[g(S)]$.

(iii) For every $A \subseteq [m]$ the count $|S \cap A|$ has the law of a sum of independent Bernoulli random variables.

(iv) Conditioning on $\{i \in S\}$ or $\{i \notin S\}$ (when of positive probability) and projecting to a subset $A$ yield strongly Rayleigh measures.

## Proof sketch

Real stability is preserved by specialization $z_i \mapsto 0$, by $\partial_{z_i}$ and by setting variables equal to $1$; this gives (iv). Specializing $z_i=t$ for $i \in A$ and $z_i=1$ otherwise gives a real-rooted univariate polynomial with nonnegative coefficients, whose roots $-r_k \le 0$ factor it as $\prod_k(p_k t+1-p_k)$, proving (iii). The Rayleigh inequality $\partial_i g\,\partial_j g \ge g\,\partial_i\partial_j g$ at $z=\mathbf{1}$ gives (i), and Borcea-Branden-Liggett derive (ii) from stability under symmetrization.

## Depends on

- [Strongly Rayleigh probability measures on subsets of a ground set](strongly-rayleigh-measure.md)
- [Negatively correlated events](../../../../Probability/correlation-inequalities/reimer-inequality/special-cases-of-reimer-s-inequality/negatively-correlated.md)

## Proof depends on

- [Real-rootedness of univariate specializations of real stable polynomials](../../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-rooted-univariate-specialization.md)
- [Real stable polynomials](../../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-stable.md)

## Sources

- Julius Borcea, Petter Branden, Thomas M. Liggett, "Negative Dependence and the Geometry of Polynomials", Journal of the American Mathematical Society (2009), arXiv:0707.2340.
