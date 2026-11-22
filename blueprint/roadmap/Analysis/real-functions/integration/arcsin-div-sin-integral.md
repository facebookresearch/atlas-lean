# Bhandari's arcsine-over-sine integral

Let $G = \sum_{n \ge 0} (-1)^n/(2n+1)^2$ be
Catalan's constant, and for $s > 0$ let $S_s = \sum_{n \ge 0} 1/(n + s)^2$. Then the integral
$\int_0^{\pi/2} \frac{\arcsin(\sin^2 x)}{\sin x}\,dx$ equals
$-2G - \frac{\pi^2}{2\sqrt 2} + \frac{S_{1/8} + S_{3/8}}{8\sqrt 2}$.

The series $S_{1/8}$ and $S_{3/8}$ are the trigamma values $\psi_1(1/8)$ and $\psi_1(3/8)$;
Catalan's constant and these trigamma values are written out as their defining series.

Proof: The route follows Bhandari's reduction to log-tangent integrals, followed by an
Abel-regularized Fourier expansion and residue-class evaluation.

## Sources

- Narendra Bhandari, "Infinite Series Associated with the Ratio and Product of Central Binomial Coefficients", Journal of Integer Sequences 25 (2022), equation (36), lines 307--309, <https://cs.uwaterloo.ca/journals/JIS/VOL25/Bhandari/bhan8.tex>.
