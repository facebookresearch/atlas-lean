# Valuation identity for the weighted product

Write $v_p(m)$ for the exponent of $p$ in $m$
and $\mu$ for the Möbius function, and set
$\nu_p(n) = \sum_{d \mid 210} \mu(d)\bigl(v_p((2100n/d)!) - v_p((1890n/d)!) -
v_p((210n/d)!)\bigr)$ and, for real $x \ge 0$,
$G(x) = \sum_{d \mid 210} \mu(d)\bigl(\lfloor 2100x/d \rfloor - \lfloor 1890x/d \rfloor -
\lfloor 210x/d \rfloor\bigr)$. If $p$ is a prime and $n$, $b$ are natural numbers with
$\lfloor \log_p (2100n) \rfloor < b$, where the floor of the logarithm is taken to be $0$ when
$n = 0$, then $\nu_p(n) = \sum_{j=1}^{b-1} G(n/p^j)$.
