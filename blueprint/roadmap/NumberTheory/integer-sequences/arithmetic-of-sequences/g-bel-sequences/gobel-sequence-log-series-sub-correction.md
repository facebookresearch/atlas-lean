# The logarithmic identity behind the Göbel error

Let $k, l \ge 2$ be natural numbers, let
$g_{k,l}$ be the $(k, l)$-Göbel sequence, and let $C > 0$ be a real number such that the real
numbers $C_{k,l}(n) = g_{k,l}(n)^{1/k^n}$ tend to $C$ as $n \to \infty$. Then for every natural
number $n \ge 1$ for which the two series below converge,

$$\sum_{m=1}^{\infty} \frac{\log(m + n)}{k^m} - \sum_{m=1}^{\infty} \frac{1}{k^m}
\log\Bigl(1 + \frac{m + n - 1}{g_{k,l}(m + n - 1)^{k-1}}\Bigr) =
k^n \bigl(\log C_{k,l}(n) - \log C\bigr).$$

## Sources

- Gima, Matsusaka, Miyazaki, and Yara, *On Integrality and Asymptotic Behavior of the (k, l)-Göbel Sequences*, Journal of Integer Sequences 27 (2024), Article 24.8.1, proof of Theorem 11 (`jis-2024-24.8.1-thm-11`).
