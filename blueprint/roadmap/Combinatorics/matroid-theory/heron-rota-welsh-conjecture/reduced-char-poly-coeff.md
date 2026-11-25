# Coefficients $\mu_k$ of the reduced characteristic polynomial

Let $M$ be a finite matroid of rank $\rho$, with characteristic polynomial $\chi_M$. For a natural
number $k$, put

$$
\mu_k(M) = (-1)^k \sum_{i=0}^{k} [\lambda^{\rho - i}] \, \chi_M(\lambda),
$$

where $[\lambda^j]\,\chi_M$ is the coefficient of $\lambda^j$ and the exponent $\rho - i$ is read
as $0$ when $i > \rho$, so that each such term repeats the constant coefficient.

When $M$ is loopless and $\rho = r + 1 \ge 1$, $\chi_M(1) = 0$ and these are the coefficients of
the reduced characteristic polynomial for $k \le r$:

$$
\overline{\chi}_M(\lambda) = \frac{\chi_M(\lambda)}{\lambda - 1}
  = \sum_{k=0}^{r} (-1)^k \mu_k(M) \, \lambda^{r-k},
$$

since dividing by $\lambda - 1$ turns coefficients into partial sums. If $M$ has a loop then
$\chi_M = 0$ and every $\mu_k(M)$ is $0$. Adiprasito, Huh and Katz note that $\mu_0(M) = 1$, that
$\mu_r(M) = |\mu_M(\emptyset, E)|$ is the absolute value of the Möbius number, and that
$\mu_k(M) = w_k(M) - w_{k-1}(M) + \cdots + (-1)^k w_0(M)$.

## Background

- [Coefficients of the characteristic polynomial of a matroid](char-poly-coeff.md): the
  coefficients $[\lambda^j]\,\chi_M$ summed here.

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Section 9.1 and Definition 9.1, https://arxiv.org/abs/1511.02888.
