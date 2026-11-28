# Polarization lemma for statistical distance

For distributions $p_0, p_1$ on a finite set and integers $\lambda, \ell, k \ge 1$, let $q_c = \mathrm{XOR}_\lambda(p_0, p_1; c)^{\otimes \ell}$ for $c \in \{0,1\}$ and define the polarized pair $r_c = \mathrm{XOR}_k(q_0, q_1; c)$. With $\delta = \delta(p_0, p_1)$,

$$
1 - 2k\exp\Big(-\frac{\ell\,\delta^{2\lambda}}{2}\Big) \le \delta(r_0, r_1) \le \big(\ell\,\delta^{\lambda}\big)^{k}.
$$

Consequently, for constants $0 \le \beta < \alpha^2 \le 1$ with $\alpha > 0$ there are constants $m \ge 1$ and $b$ such that with $\lambda = m(\lfloor\log_2 k\rfloor + 1)$ and $\ell = 2^{b(\lfloor\log_2 k\rfloor + 1)}$ (both polynomial in $k$), every pair with $\delta \ge \alpha$ is mapped to a pair at distance at least $1 - 2^{-k}$ and every pair with $\delta \le \beta$ to a pair at distance at most $2^{-k}$.

## Proof sketch

By the XOR lemma, $\delta(q_0, q_1)$ lies between the direct-product lower bound $1 - 2e^{-\ell\delta^{2\lambda}/2}$ and $\ell\delta^\lambda$; applying the XOR lemma again raises this to the $k$-th power. The upper bound is immediate, and the lower bound uses $(1 - x)^k \ge 1 - kx$. With $\beta < \alpha^2$, choosing $\lambda$ and $\ell$ as stated makes $\ell\beta^\lambda \le 1/2$ while $\ell\alpha^{2\lambda}$ grows like a large multiple of $k$, which yields both $2^{-k}$ errors.

## Depends on

- [XOR construction of two distributions](xor-construction.md)
- [Total variation distance between finite measures](../../convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Proof depends on

- [XOR lemma for statistical distance](xor-lemma-for-statistical-distance.md)
- [Direct product lemma for statistical distance](direct-product-lemma.md)

## Sources

- A. Sahai and S. Vadhan, "A Complete Problem for Statistical Zero Knowledge", Journal of the ACM 50(2), 2003.
