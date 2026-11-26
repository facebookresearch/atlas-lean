# Erdős Problem 793 has a positive answer

Let $F(n)$ be the largest size of a set
$A \subseteq \{1, \dots, n\}$ such that $a \nmid bc$ whenever $a, b, c \in A$ with $a \ne b$ and
$a \ne c$ ($b = c$ is allowed), and let $\pi(n)$ be the number of primes at most $n$. Then there
is a real constant $C > 0$ such that $(F(n) - \pi(n)) / (n^{2/3} / (\log n)^2) \to C$ as
$n \to \infty$.

This holds with $C = 27/2$; the result is credited to GPT-5.6 Sol (prompted by Chojecki), and the proof is
written up in Chojecki (2026, Theorem 1.1).

## Sources

- Przemek Chojecki, *The Second Term for Strongly 2-Primitive Sets*, arXiv:2607.15306 (2026), https://arxiv.org/abs/2607.15306.
- T. F. Bloom, Erdős Problem #793, https://www.erdosproblems.com/793.
