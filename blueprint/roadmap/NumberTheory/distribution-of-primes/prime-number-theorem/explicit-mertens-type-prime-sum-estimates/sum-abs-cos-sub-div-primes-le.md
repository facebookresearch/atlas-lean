# Explicit bound for a cosine-weighted sum over primes

Let $K$ be a real number with
$\frac{1}{2\pi} \int_0^{2\pi} |\cos t - K| \, dt = 1 - K$ (this equation has exactly one real
solution, $K \approx 0.3286$). Then for every real $\alpha$ with $0 < \alpha \le 1$ and every real
$\tau$, $\sum_{p \le e^{1/\alpha}} |\cos(\tau \log p) - K|/p \le (1 - K) \log(1/\alpha) +
(2 + 2K) \log \log(|\tau| + 3) + 7.28$, where the sum runs over the primes $p \le e^{1/\alpha}$.

## Sources

- Matteo Bordignon and Forrest J. Francis, *Explicit Improvements to the Burgess Bound via Pólya--Vinogradov*, INTEGERS 24 (2024), Article A66, Lemma 7.
