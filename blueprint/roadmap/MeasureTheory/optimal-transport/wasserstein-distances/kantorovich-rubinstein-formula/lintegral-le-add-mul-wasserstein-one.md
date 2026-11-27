# Lipschitz test functions are controlled by $W_1$

On a second-countable pseudo-extended metric space whose σ-algebra contains the open sets, let
$g : X \to [0, \infty)$ be $K$-Lipschitz with $K \ge 0$. Then for all probability measures $\mu, \nu$,

$$\int g \, d\mu \le \int g \, d\nu + K \, W_1(\mu, \nu).$$

Both sides are taken in $[0, \infty]$. For each coupling $\pi$ of $\mu$ and $\nu$, integrating
$g(x) \le g(y) + K\, d(x, y)$ against $\pi$ gives
$\int g\,d\mu \le \int g\,d\nu + K \int d(x, y)\,d\pi(x, y)$; take the infimum over $\pi$. For
probability measures with finite first moments this is the elementary half of the
Kantorovich–Rubinstein formula
$W_1(\mu, \nu) = \sup_{\|\psi\|_{\mathrm{Lip}} \le 1} \bigl(\int \psi \, d\mu - \int \psi \, d\nu\bigr)$, whose
other half needs Kantorovich duality.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Remark 6.5, formula (6.3).
