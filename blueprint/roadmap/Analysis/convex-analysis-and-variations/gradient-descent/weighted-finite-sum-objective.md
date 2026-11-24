# Weighted finite-sum objective

Let $n \ge 1$, let $f_i:\mathbb R^d\to\mathbb R$ for $i=1,\ldots,n$, and
let $v=(v_1,\ldots,v_n)\in\mathbb R^n$ be a vector of weights. Define the
weighted objective $f_v$ and the original objective $f$ by

$$
f_v(x)=\frac{1}{n}\sum_{i=1}^n v_i f_i(x),
\qquad f(x)=\frac{1}{n}\sum_{i=1}^n f_i(x).
$$

## Depends on

No prerequisites beyond the finite family of real-valued functions and weights specified above.

## Proof depends on

None; this page is a definition.

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 1, equation (1), and Section 1.2, the formula
  inside the expectation in equation (4).
