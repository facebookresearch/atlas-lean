# Maximum-likelihood decoding errs only on ties or worse

Let $g$ be a maximum-likelihood decoder for the code $C = (x_1, \dots, x_M)$: for every output $y$,
$W^N(y \mid x_m) \le W^N(y \mid x_{g(y)})$ for all $m$. Then, under the product law
$W^{\otimes N}(\cdot \mid x_m)$ on output words,

$$\Pr\big[g(Y) \ne m\big] \le P_{e,m}(C),$$

the [error probability with ties counted as errors](../random-coding-bound-and-gallager-s-exponent/ml-error-prob.md):
when $g(y) = m' \ne m$, the word $x_{m'}$ is at least as likely as $x_m$. The product measure of a
finite set of output words is the sum of the products $\prod_i W(y_i \mid x_{m,i})$ over the set.

## Background

- [Error probability of maximum-likelihood decoding](../random-coding-bound-and-gallager-s-exponent/ml-error-prob.md)
- [Block transition probability of a memoryless channel](../random-coding-bound-and-gallager-s-exponent/block-transition.md)
