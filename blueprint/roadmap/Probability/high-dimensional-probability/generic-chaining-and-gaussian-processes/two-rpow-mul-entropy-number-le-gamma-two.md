# Entropy numbers are controlled by $\gamma_2$

For every distance and every $n$, $2^{n/2} e_n(T) \le \gamma_2(T, d)$ (Talagrand, *Upper and
Lower Bounds for Stochastic Processes*, 2nd ed., 2021, Exercise 2.7.8 (a), (2.57), where the
constant is a universal $L$; here it is $1$). Given an admissible sequence, one point from each
cell of $\mathcal{A}_n$ gives at most $N_n$ centres, each $t$ lying within $\Delta(A_n(t))$ of its
own, and $2^{n/2}\Delta(A_n(t))$ is one term of the series defining $\gamma_2$. The space need not
be finite.

## Background

- [Sudakov minoration](sudakov-minoration.md): Talagrand's Exercise 2.10.3 restates it as
  $e_n(T, d) \le L\,2^{-n/2}\,\mathbb{E}\sup_t X_t$ for a Gaussian process, the companion of this
  inequality under the majorizing measure theorem.
