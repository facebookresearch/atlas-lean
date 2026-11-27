# Kantorovich duality on compact metric spaces

Let $X$ and $Y$ be nonempty compact metric
spaces, each carrying its Borel $\sigma$-algebra, let $\mu$ and $\nu$ be probability measures on
$X$ and $Y$, and let $c : X \times Y \to \mathbb{R}$ be continuous. Then the infimum of
$\int c \, d\pi$ over all couplings $\pi$ of $\mu$ and $\nu$ equals the supremum of
$\int \varphi \, d\mu + \int \psi \, d\nu$ over all pairs of continuous functions
$\varphi : X \to \mathbb{R}$ and $\psi : Y \to \mathbb{R}$ such that
$\varphi(x) + \psi(y) \le c(x, y)$ for all $x \in X$ and $y \in Y$.

This is the case of Villani's Theorem 5.10(i) where $X$ and $Y$ are compact and $c$ is continuous
(hence bounded), written with $\varphi(x) + \psi(y) \le c(x, y)$ in place of Villani's
$\varphi(y) - \psi(x) \le c(x, y)$. Its case of nonnegative lower semicontinuous costs on Polish
spaces is recorded as [Kantorovich duality for lower semicontinuous costs](kantorovich-duality-lsc.md).

## Sources

- L. V. Kantorovich, On the Translocation of Masses (1942); English transl. J. Math. Sci. 133 (2006), 1381-1382, DOI 10.1007/S10958-006-0049-2; modern ref C. Villani, Topics in Optimal Transportation (2003).
- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Theorem 5.10(i).
