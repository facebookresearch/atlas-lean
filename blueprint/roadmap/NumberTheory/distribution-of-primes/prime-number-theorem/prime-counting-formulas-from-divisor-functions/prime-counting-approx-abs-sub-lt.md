# Prime-counting function from the smooth divisor count

For a natural number $k$ let

$$\tilde\tau(k) = \sum_{j=1}^{k} \exp\left(-\frac{\pi^2}{2} k j^3 \sin^2\frac{k\pi}{j}\right),$$

and for $n \ge 2$ let $\tilde\pi(n) = \sum_{k=2}^{n} e^{-k(\tilde\tau(k) - 2)}$. Then for every
natural number $n \ge 2$, $|\tilde\pi(n) - \pi(n)| < 0.7129749140934$, where $\pi(n)$ is the
number of primes at most $n$.

The constant is $0.684 + 1/(e^3(e - 1))$ truncated to thirteen decimal places, the sum of the
two one-sided bounds, as the two-sided bound requires.

## Sources

- Carlos M. Alberto and Mavacala N. Saidi, *A New Asymptotic Formula for π(n) with the Divisor Counting Function*, INTEGERS 26 (2026), Article A46, Theorem 2 (`integers-2026-A46-thm-2`).
