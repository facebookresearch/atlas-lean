# Kantorovich duality for lower semicontinuous costs

Let $X$ and $Y$ be Polish spaces (complete separable metric spaces with their Borel σ-algebras),
let $\mu$ and $\nu$ be probability measures on $X$ and $Y$, and let $c : X \times Y \to [0, \infty]$ be
lower semicontinuous. Then

$$\inf_{\pi} \int_{X \times Y} c \, d\pi \;=\; \sup \Bigl\{ \int_Y \varphi \, d\nu - \int_X \psi \, d\mu \Bigr\},$$

where the infimum runs over the couplings $\pi$ of $\mu$ and $\nu$, and the supremum over pairs of
bounded continuous functions $\psi : X \to \mathbb{R}$ and $\varphi : Y \to \mathbb{R}$ with
$\varphi(y) - \psi(x) \le c(x, y)$ for all $x, y$. Both sides may be $+\infty$.

This is the first equality of Theorem 5.10(i) in the case $a = b = 0$ of the lower bound
$c(x, y) \ge a(x) + b(y)$. Villani also shows that the supremum may be taken over integrable or
$c$-convex potentials, and parts (ii) and (iii) characterise optimal couplings by $c$-cyclical
monotonicity and give the existence of optimal potentials. For the
[compact, continuous-cost case](kantorovich-duality-compact.md) see its own statement (with the sign convention
$\varphi(x) + \psi(y) \le c(x, y)$).

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 5.10(i).
