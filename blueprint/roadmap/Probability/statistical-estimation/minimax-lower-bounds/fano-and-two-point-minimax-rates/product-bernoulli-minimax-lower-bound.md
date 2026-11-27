# Minimax lower bounds for estimating a product-Bernoulli mean vector

Let $\iota$ be a finite index set of size $d$, $n \ge 1$, and let $\hat p$ be any (possibly randomized) estimator mapping $n$ i.i.d. observations from the product of Bernoulli laws with mean vector $p \in [0,1]^\iota$ to $\mathbb{R}^\iota$. Then

$$
\sup_{p} \mathbb{E}_p\,\|\hat p - p\|_2^2 \ge \frac{d}{72 n}, \qquad \sup_p \mathbb{E}_p\,\|\hat p - p\|_1 \ge \frac{d}{12\sqrt n}.
$$

## Proof sketch

Use Assouad's lemma on the hypercube of mean vectors with coordinates $1/2$ or $1/2 + \delta$: both losses decompose coordinatewise, and flipping one coordinate changes the law by a single Bernoulli factor whose $n$-sample divergence is $O(n\delta^2)$. Each coordinate contributes the one-dimensional Le Cam bound, so the risk is $d$ times the Bernoulli rate.

## Depends on

- [Assouad's lemma](../mul-one-sub-le-minimax.md)

## Proof depends on

- [Assouad's lemma](../mul-one-sub-le-minimax.md)
- [Minimax lower bounds for estimating a Bernoulli mean](bernoulli-mean-minimax-lower-bound.md)

## Sources

- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
