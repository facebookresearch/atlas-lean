# The expected complete-data log-likelihood

For a finite state set $I$, a real matrix $n$ (expected substitution counts), real functions $\tau$ (expected state durations) and $r$ (root posterior), a real matrix $Q$ and real weights $\pi$, put

$$\ell(Q, \pi) = \sum_{a \ne b} n_{ab} \log Q_{ab} + \sum_a \tau_a Q_{aa} + \sum_b r_b \log \pi_b,$$

with the conventions $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$ (Garber et al. 2009, Eq. 6).

It is the expected complete-data log-likelihood of a substitution process with rate matrix $Q$ and root distribution $\pi$ when $Q_{ab} > 0$ for every $a \ne b$ with $n_{ab} \ne 0$ and $\pi_b > 0$ for every $b$ with $r_b \ne 0$; otherwise the probabilistic value is $-\infty$ and differs from the value given by the conventions.

## Sources

- M. Garber, M. Guttman, M. Clamp, M. C. Zody, N. Friedman, X. Xie, *Identifying novel constrained elements by exploiting biased substitution patterns*, Bioinformatics 25 (2009), i54–i62, Eq. 6.
