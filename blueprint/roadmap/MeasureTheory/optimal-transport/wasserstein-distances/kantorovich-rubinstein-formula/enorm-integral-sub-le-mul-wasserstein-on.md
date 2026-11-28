# Kantorovich–Rubinstein bound for real Lipschitz functions

On a second-countable pseudo-extended metric space whose σ-algebra contains the open sets, let
$f : X \to \mathbb{R}$ be $L$-Lipschitz and integrable for the probability measures $\mu$ and $\nu$.
Then

$$\Bigl| \int f \, d\mu - \int f \, d\nu \Bigr| \le L \, W_1(\mu, \nu).$$

For every coupling $\pi$, $\int f\,d\mu - \int f\,d\nu = \int (f(x) - f(y))\,d\pi(x, y)$, whose absolute
value is at most $L \int d(x, y)\,d\pi$. For $L = 1$ this is the inequality $\ge$ in the
[Kantorovich–Rubinstein formula](wasserstein-one-eq-i-sup-lipschitz.md).

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Remark 6.5, formula (6.3).
