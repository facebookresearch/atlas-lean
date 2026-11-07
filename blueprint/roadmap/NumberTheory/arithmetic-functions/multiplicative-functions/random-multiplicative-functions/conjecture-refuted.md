# No iterated-logarithm constant for Rademacher multiplicative functions

The Rademacher
LIL constant conjecture is false: there is no real constant $c > 0$ such that, for every
probability space $(\Omega, \mu)$ and every family $(X_p)_p$ of independent, measurable random
signs indexed by the primes, each uniform on $\{-1, 1\}$, for $\mu$-almost every $\omega$ the
limit superior as $N \to \infty$ of $S_N(\omega) / \sqrt{N \log \log N}$ equals $c$. Here
$S_N(\omega) = \sum_{m=1}^{N} f_\omega(m)$, where $f_\omega$ is the Rademacher random
multiplicative function: $f_\omega(m) = \prod_{p \mid m} X_p(\omega)$ for squarefree $m$ and
$f_\omega(m) = 0$ otherwise.

Durkan and Pearce-Crump, and independently Verreault, proved that for every $\varepsilon > 0$,
almost surely $|\sum_{n \le x} f_\omega(n)| \ll \sqrt{x} (\log \log x)^{1/4 + \varepsilon}$ as
$x \to \infty$, so the normalized limit superior is almost surely $0$.

## Sources

- B. Durkan, A. Pearce-Crump, A sharp almost sure upper bound for partial sums of random multiplicative functions, arXiv preprint (2026), arXiv:2607.29429, https://arxiv.org/abs/2607.29429; W. Verreault, Almost sure upper bound for sums of random multiplicative functions and critical chaos, arXiv preprint (2026), arXiv:2608.21354, https://arxiv.org/abs/2608.21354. Moved from `OpenConjectures/NumberTheory/RademacherLILConstant`.
