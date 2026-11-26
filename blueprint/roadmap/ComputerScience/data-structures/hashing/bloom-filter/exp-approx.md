# Exponential approximation of the Bloom filter false-positive rate

For natural numbers $m$ and $n$ and a real number $\kappa$ (a real number of hash functions), the
exponential approximation of the false-positive rate is the real power

$$\left(1 - e^{-\kappa n / m}\right)^{\kappa},$$

where the quotient by $m$ is taken to be $0$ when $m = 0$. The base $1 - e^{-\kappa n / m}$ lies in
$(0, 1)$ when $\kappa n / m > 0$; otherwise it is at most $0$, and the real power follows the
usual conventions $0^0 = 1$, $0^{\kappa} = 0$ for $\kappa \ne 0$, and
$x^{\kappa} = e^{\kappa \log |x|} \cos(\pi \kappa)$ for $x < 0$.
