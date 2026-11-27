# Upper bound for twisted prime sums with real coefficients

Throughout, sums over $p$ run
over primes. Let $K$ be a real number with
$\frac{1}{2\pi} \int_0^{2\pi} |\cos t - K| \, dt = 1 - K$. Let $g$ be a real-valued function on
the natural numbers with $|g(p)| \le 1$ for every prime $p$, let $\alpha$ be a real number with
$0 < \alpha \le 1$, put $x = e^{1/\alpha}$, and let $\lambda$ be a real number with
$\sum_{p \le x} (1 - g(p))/p = \lambda \sum_{p \le x} 1/p$. Let $M$ be the Meissel–Mertens
constant and $M'(x) = \sum_{p \le x} 1/p - \log \log x - M$. Then for every real $\tau$,
$\operatorname{Re} \sum_{p \le x} g(p)/p^{1 + i\tau}$ is at most
$(1 - K\lambda) \log(1/\alpha) + (2 + 2K) \log \log(|\tau| + 3) + 7.28 +
(K - K\lambda)(M + M'(x))$.

The paper prints $(2 + 2K)(\log \log |\tau| + 3)$; its proof applies Lemma 7, which has
$\log \log(|\tau| + 3)$, and the printed form fails at $\alpha = 1$, $g \equiv 1$,
$\tau = 1.0001$. The paper allows $\alpha \in [0, 1]$; here $\alpha > 0$, where $e^{1/\alpha}$
is defined.

## Sources

- Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 8.
