# Minimax lower bounds for estimating a Bernoulli mean

Let $n \ge 1$ and let $\hat p$ be any (possibly randomized) estimator that maps $n$ independent flips of a coin with unknown bias $p \in [0,1]$ to a real number. Then

$$
\sup_{p \in [0,1]} \mathbb{E}_p\bigl[(\hat p - p)^2\bigr] \ge \frac{1}{72 n}, \qquad \sup_{p \in [0,1]} \mathbb{E}_p\,|\hat p - p| \ge \frac{1}{12\sqrt n}.
$$

## Proof sketch

Apply Le Cam's two-point method to biases $1/2$ and $1/2 + \delta$ with $\delta$ of order $1/\sqrt n$. The Kullback-Leibler divergence between the two $n$-flip product laws is $O(n\delta^2)$, so by Pinsker the total variation stays bounded away from $1$, and every estimator incurs error at least a constant times $\delta$ (squared: $\delta^2$) at one of the two points; optimizing $\delta$ gives the constants.

## Depends on

- [Le Cam's two-point lower bound](../mul-one-sub-total-variation-dist-le-mini.md)

## Proof depends on

- [Le Cam's two-point lower bound](../mul-one-sub-total-variation-dist-le-mini.md)
- [Pinsker's inequality for finite probability mass functions](../../../../InformationTheory/not-yet-classified/part-02/pinsker-pmf.md)
- [Kullback–Leibler divergence on a finite space](../../../../InformationTheory/entropy-and-mutual-information/shannon-entropy-and-kullback-leibler-divergence/to-real-kl-div-eq-sum.md)

## Sources

- Lucien Le Cam, "Convergence of Estimates Under Dimensionality Restrictions", The Annals of Statistics 1(1), 1973.
- Alexandre B. Tsybakov, "Introduction to Nonparametric Estimation", Springer, 2009.
