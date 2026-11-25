# Characteristic function of a sum of independent random variables

If $X_1$ and $X_2$ are independent real random variables with characteristic functions $\varphi_1$ and
$\varphi_2$, then $X_1 + X_2$ has characteristic function $\varphi_1 \varphi_2$. The second statement of this card is
the same identity for independent random vectors in a real inner product space with a second countable topology,
under a finite measure, stated for the characteristic functions of their laws.

## Idea

The distribution of a sum of independent random variables is a convolution, and characteristic functions
turn convolution into multiplication; by induction, $X_1 + \dots + X_n$ has characteristic function
$\varphi_{X_1} \cdots \varphi_{X_n}$ for independent $X_k$. For example, the sum of independent normal variables with
means $m_1, m_2$ and variances $\sigma_1^2, \sigma_2^2$ has characteristic function
$e^{i (m_1 + m_2) t - (\sigma_1^2 + \sigma_2^2) t^2 / 2}$, so by the inversion formula it is normal with mean $m_1 + m_2$
and variance $\sigma_1^2 + \sigma_2^2$.

## Statements

- [Characteristic function of a sum of independent random variables](characteristic-function-independent-sum.md)
- [Characteristic function of a sum of independent random vectors](char-fun-map-add-eq-mul.md): more general: independent random vectors in a real inner product space

## Background

- [Characteristic function](../characteristic-functions-of-finite-measures/characteristic-function/README.md): characteristic functions
- [Independence](../../foundations/independent-events-and-random-variables/independence/README.md): independent random variables
- [Inversion formula for characteristic functions](../characteristic-functions-of-finite-measures/inversion-formula/README.md): uniqueness, used in the example
