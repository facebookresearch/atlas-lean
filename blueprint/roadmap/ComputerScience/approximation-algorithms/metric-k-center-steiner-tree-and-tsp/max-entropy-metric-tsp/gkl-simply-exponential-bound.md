# Simply exponential joint count bound for strongly Rayleigh measures (Gurvits-Klein-Leake)

Let $\mu$ be strongly Rayleigh on $2^{[m]}$, let $A_1,\dots,A_n$ count elements in disjoint subsets of $[m]$, fix $\kappa \in \mathbb{Z}_{\ge 0}^{n}$ and $\epsilon \in (0,1]$. If

$$
\big|\mathbb{E}_\mu[A_I]-\kappa_I\big| \le 1-\epsilon \qquad \text{for all}\ I \subseteq [n],
$$

where $A_I=\sum_{i \in I}A_i$ and $\kappa_I=\sum_{i \in I}\kappa_i$, then

$$
\mathbb{P}_\mu[A_1=\kappa_1,\dots,A_n=\kappa_n] \ge \epsilon^{n}\prod_{i:\,\kappa_i > 0}\frac{1}{e\sqrt{\kappa_i}} .
$$

The dependence on $\epsilon$ is tight for every fixed $\kappa$ with strictly positive entries.

## Proof sketch

Encode the counts by the real stable polynomial $p(t_1,\dots,t_n)=\mathbb{E}[\prod_i t_i^{A_i}]$, so the target probability is a coefficient of $p$. Productization reduces coefficient lower bounds for real stable polynomials to products of affine linear forms with an underlying matrix structure. Worst cases are characterized by bipartitioned forests, giving a clean induction that loses one factor $\epsilon$ per block.

## Depends on

- [Strongly Rayleigh probability measures on subsets of a ground set](strongly-rayleigh-measure.md)

## Proof depends on

- [Real stable polynomials](../../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-stable.md)

## Sources

- Leonid Gurvits, Nathan Klein, Jonathan Leake, "From Trees to Polynomials and Back Again: New Capacity Bounds with Applications to TSP", ICALP (2024), arXiv:2311.09072.
