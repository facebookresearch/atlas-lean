# Common-ancestor regimes under power-law seed-bank ages

In the [renewal seed-bank model](kingman-limit-of-the-renewal-seed-bank-ancestral-process.md) with population size $N$, let the seed-bank age distribution have a regularly varying tail,

$$\mu(\{n, n+1, \dots\}) = n^{-\alpha} L(n), \qquad n \in \mathbb N,$$

with $\alpha \in (0,\infty)$ and $L$ slowly varying (write $\mu \in \Gamma_\alpha$). Let $A(v)$ be the ancestral line of individual $v$, $q_n$ the renewal sequence of $\mu$, and $\tau$ the time to the most recent common ancestor of two distinct individuals $v,w$ of the same generation.

**Theorem (three regimes).** For every $N$:

1. if $\alpha \in (0, \tfrac12)$, then $\mathbb P(A(v) \cap A(w) \neq \emptyset) < 1$: with positive probability two individuals never share an ancestor;
2. if $\alpha \in (\tfrac12, 1)$, then $\mathbb P(A(v) \cap A(w) \neq \emptyset) = 1$ but $\mathbb E[\tau] = \infty$;
3. if $\alpha > 1$, then $\mathbb P(A(v) \cap A(w) \neq \emptyset) = 1$ and $\mathbb E[\tau]/N \to (\mathbb E_\mu \eta)^2$ as $N \to \infty$.

**Theorem (equilibrium correlations).** Let the forward process be started in the equilibrium $\lambda^p_N$ with type frequency $p$, and let $Y_N(i)$ be the type of an individual in generation $i$. Then $\mathbb E[Y_N(i)] = p$ for all $i$, and:

- if $\alpha > \tfrac12$, $\mathrm{Cov}(Y_N(0), Y_N(i)) = p(1-p)$ for all $i$ and $N$, i.e. the equilibrium is a mixture of the two monomorphic states;
- if $\alpha \in (0,\tfrac12)$, $\mathrm{Cov}(Y_N(v), Y_N(w)) = p(1-p)\,\dfrac{\sum_{n\ge0} q_n q_{n + i_v - i_w}}{N + \sum_{n\ge1} q_n^2}$ for $v \neq w$, the covariance vanishes as $N\to\infty$, while the correlation has a limit $C(i) \in (0,1)$ with $C(i) \asymp i^{2\alpha - 1} L(i)$ as $i \to \infty$.

Thus genetic variability can be maintained without mutation when the seed bank is heavy enough ($\alpha < 1/2$), and fixation still occurs but with infinite mean time when $1/2 < \alpha < 1$.

## Depends on

- [Kingman limit of the renewal seed-bank ancestral process](kingman-limit-of-the-renewal-seed-bank-ancestral-process.md)

## Expansion

Two ancestral lines meet only when both renewal processes visit the same generation and then pick the same individual, so the expected number of shared ancestors is $N^{-1}\sum_n q_n^2$. For $\mu \in \Gamma_\alpha$ with $\alpha < 1$, the renewal theorem for infinite-mean laws gives $\sum_{n\le i} q_n \sim c\, i^{\alpha}/L(i)$, so $\sum_n q_n^2 < \infty$ exactly when $\alpha < 1/2$; finiteness gives a positive probability of no meeting (a Borel–Cantelli argument in the style of Hammond and Sheffield), and divergence gives almost sure meeting. When $1/2 < \alpha < 1$ the lines meet but the waiting time inherits the infinite mean of $\mu$. The covariance formula comes from conditioning on whether the two lines merge, and the asymptotics of $\sum_n q_n q_{n-i}$ give the power-law decay of $C(i)$.

## Sources

- Jochen Blath, Adrián González Casanova, Noemi Kurt, Dario Spanò, "The ancestral process of long term seed bank models", published as "The Ancestral Process of Long-Range Seed Bank Models", *Journal of Applied Probability* 50 (2013), 741–759, <https://doi.org/10.1239/jap/1378401233>; preprint arXiv:1203.5202, <https://doi.org/10.48550/arXiv.1203.5202>. Numbering of the arXiv version: Section 2 (definition of $\Gamma_\alpha$, Theorem 2.2, Theorem 2.7), Section 3 (Lemmas 3.6 and 3.7), Section 4 (Proposition 4.2).
