# Stirling decomposition of the binomial-to-Gaussian ratio

Let $0 < k < n$ be natural numbers, let $b(n, k) = \binom{n}{k} 2^{-n}$ be the [binomial point
mass](binom-prob-half.md) and $g(n, k)$ its [Gaussian approximation](gaussian-approx-half.md),
and let $s_m = m! \big/ \big(\sqrt{2m}\,(m/e)^m\big)$ be the Stirling sequence. Then

$$\frac{b(n, k)}{g(n, k)} = \frac{s_n}{s_k\, s_{n-k}} \cdot \sqrt{\frac{\pi n^2}{4 k (n - k)}} \cdot \frac{n^n}{k^k (n - k)^{n-k}\, 2^n} \cdot \exp\Big(\frac{(k - n/2)^2}{n/2}\Big).$$
