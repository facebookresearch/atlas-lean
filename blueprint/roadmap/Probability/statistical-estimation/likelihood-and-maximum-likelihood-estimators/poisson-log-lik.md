# Poisson log-likelihood of counts

For a finite index set $\iota$, real means $E : \iota \to \mathbb{R}$ and counts $k : \iota \to \mathbb{N}$, the Poisson log-likelihood is

$$\ell(E, k) = \sum_{i \in \iota} \bigl(k_i \log E_i - E_i - \log k_i!\bigr),$$

with the convention $\log 0 = 0$ and $\log x = \log|x|$ for $x < 0$; it is meaningful for $E_i > 0$.
