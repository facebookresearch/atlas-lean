# Unbiasedness of the AMS estimator

Let $\mu$ be a probability measure on $\Omega$, $\iota$ a finite set, and $(\varepsilon_i)_{i \in \iota}$ measurable random variables with values in $\{-1, 1\}$, mean $0$, and [four-wise independent](four-wise-independent.md): any family of at most four of them is mutually independent. Then for all real weights $(m_i)_{i \in \iota}$, the random variable $Z = \sum_i m_i \varepsilon_i$ satisfies

$$\mathbb{E}[Z^2] = \sum_{i \in \iota} m_i^2$$

(N. Alon, Y. Matias and M. Szegedy, *J. Comput. System Sci.* 58 (1999), proof of Theorem 2.2; the source notes that pairwise independence suffices for this step).
