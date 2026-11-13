# Birkhoff's ergodic theorem in $L^1$ for bounded functions

Let $\mu$ be a probability
measure on a measurable space $\alpha$, let $T : \alpha \to \alpha$ be ergodic with respect to
$\mu$ (in particular $T$ preserves $\mu$), let $M \ge 0$, and let $g : \alpha \to \mathbb{R}$ be
$\mu$-integrable with $|g(x)| \le M$ for every $x \in \alpha$. For $n \ge 1$ let
$A_n g(x) = \frac{1}{n} \sum_{k=0}^{n-1} g(T^k x)$. Then
$\int \left| A_n g(x) - \int g \, d\mu \right| d\mu(x) \to 0$ as $n \to \infty$.

This follows from the almost-everywhere ergodic theorem and dominated convergence.
