# Outcome distribution of Shor period finding when the order divides q

In the setting of the Shor period-finding page, suppose the order $r$ divides $q$. Then the measurement returns $(c, x^k \bmod N)$, with $0 \le c < q$ and $0 \le k < r$,
with probability $1/r^2$ if $c$ is a multiple of $q/r$, that is $c = dq/r$ for some $0 \le d < r$, and with probability $0$ otherwise. In particular the marginal law of $c$ is
uniform on the $r$ multiples of $q/r$, and $c/q = d/r$ exactly.

## Proof

With $\omega = e^{2\pi i/q}$, the amplitude of $\lvert c \rangle \lvert x^k \rangle$ after the Fourier transform is $\frac1q \sum_{a \equiv k \ (\mathrm{mod}\ r)} \omega^{ac}$, a sum over the $q/r$ values
$a = k + jr$, equal to $\frac1q \omega^{kc} \sum_{j=0}^{q/r - 1} \omega^{jrc}$. The geometric sum is $q/r$ when $\omega^{rc} = 1$, that is when $q$ divides $rc$, equivalently $q/r$ divides $c$,
and $0$ otherwise. The probability is therefore $(q/r)^2/q^2 = 1/r^2$ on the $r \cdot r$ outcomes with $q/r \mid c$, which sum to $1$.

## Depends on

- [Shor period finding: outcome distribution and order recovery](shor-period-finding-outcome-distribution-and-order-recovery.md)

## Sources

- P. W. Shor, *Polynomial-time algorithms for prime factorization and discrete logarithms on a quantum computer*, SIAM J. Computing 26(5) (1997); arXiv:quant-ph/9508027, Section 5 (the outcome probabilities; the case in which $r$ divides $q$ is the exact special case). Background reference. <https://arxiv.org/abs/quant-ph/9508027>
