# (2,4)-Hypercontractivity Theorem

For every $f : \{-1, 1\}^n \to \mathbb{R}$,

$$\|T_{1/\sqrt3}\, f\|_4 \le \|f\|_2, \qquad\text{stated as}\qquad
\mathbb{E}\big[(T_{1/\sqrt3} f)^4\big] \le \mathbb{E}[f^2]^2 .$$

It follows from the $(4/3, 2)$ case $\|T_{1/\sqrt3} f\|_2 \le \|f\|_{4/3}$ by duality. With
$h = T_\rho f$ and $\rho = 1/\sqrt3$, self-adjointness of $T_\rho$ and Cauchy–Schwarz give
$\mathbb{E}[h^4] = \mathbb{E}[f \cdot T_\rho(h^3)] \le \|f\|_2 \|T_\rho(h^3)\|_2 \le \|f\|_2 \|h^3\|_{4/3}
= \|f\|_2\, \mathbb{E}[h^4]^{3/4}$.

## Sources

- R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University Press, 2014 (arXiv:2105.10386), (2,4)-Hypercontractivity Theorem, Section 9.2; the duality is Proposition 9.19.
