# Boundary fixed points and bifurcations of the coupled logistic predator–prey map

Let prey $x_n$ and predators $y_n$ evolve by

$$x_{n+1} = a\,x_n(1 - x_n) - c\,x_n y_n, \qquad y_{n+1} = b\,y_n(1 - y_n) + d\,x_n y_n,$$

with $a, b, c, d > 0$. A fixed point with Jacobian eigenvalues $R_1, R_2$ is a sink if $|R_1|, |R_2| < 1$, a source if both exceed one in modulus, a saddle if one is below and one above, and non-hyperbolic if some $|R_i| = 1$. Then:

1. The origin $P_0 = (0, 0)$ has eigenvalues $a$ and $b$: it is a sink for $a, b < 1$, a saddle when exactly one of $a, b$ exceeds $1$, and a source for $a, b > 1$; at $a = 1$ ($b \ne 1$) it undergoes a transcritical bifurcation.
2. The predator-free point $P_1 = \bigl(\tfrac{a-1}{a}, 0\bigr)$ has eigenvalues $2 - a$ and $b + d\,\tfrac{a-1}{a}$; for $a > 1$ it is a sink iff $1 < a < 3$ and $b < \tfrac{a + d - ad}{a}$. The source's Theorem 2 prints "$P_1$ is a sink if $1<a<3$ and $0<b<\min\{d/a-1-d,\ d/a+1-d\}$", a condition that is empty for $a>1$, because the first entry $d/a-1-d=-1-d\,\tfrac{a-1}{a}$ is negative; the page's bound $\tfrac{a+d-ad}{a}$ is the second entry $d/a+1-d$ alone, which is what the displayed eigenvalues give, since $|2-a|<1$ iff $1<a<3$ and $0<b+d\,\tfrac{a-1}{a}<1$ iff $b<\tfrac{a+d-ad}{a}$. It undergoes a transcritical bifurcation at $b = \tfrac{a + d - ad}{a}$ and a period-doubling bifurcation at $b = \tfrac{d - a - ad}{a}$ (for $a \ne 1, 3$).
3. The prey-free point $P_2 = \bigl(0, \tfrac{b-1}{b}\bigr)$ has eigenvalues $a - c\,\tfrac{b-1}{b}$ and $2 - b$; it undergoes a transcritical bifurcation at $a = \tfrac{bc + b - c}{b}$ and a period-doubling bifurcation at $a = \tfrac{bc - b - c}{b}$ (for $b \ne 1, 3$).

The unique positive fixed point, when it exists, can undergo period-doubling and Neimark–Sacker bifurcations as $a$ varies, and for suitable parameters it is a snapback repeller, so the map is chaotic in the sense of Marotto.

## Expansion

The Jacobian is $\begin{pmatrix} a(1 - 2x) - cy & -cx \\ dy & b(1 - 2y) + dx\end{pmatrix}$, which is diagonal at $P_0$ and triangular at $P_1$ and $P_2$, so the eigenvalues can be read off. A transcritical bifurcation occurs where an eigenvalue crosses $+1$ (the boundary point exchanges stability with the interior point that passes through it) and a flip where it crosses $-1$; the source verifies nondegeneracy by centre-manifold reduction. The interior bifurcations are derived from the trace–determinant conditions of the Jacobian at the positive fixed point.

## Sources

- M. O. Al-Kaff, H. A. El-Metwally, A. A. Elsadany and E. M. Elabbasy, "Exploring chaos and bifurcation in a discrete prey–predator based on coupled logistic map", Scientific Reports 14 (2024) 16118, <https://doi.org/10.1038/s41598-024-62439-8>, PMCID PMC11245555. Lemma 1, Definition 1 and Theorems 1–13.
