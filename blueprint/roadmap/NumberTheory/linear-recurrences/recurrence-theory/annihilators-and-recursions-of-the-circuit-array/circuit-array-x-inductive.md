# Column recursion for the one-variable circuit array

Extend the one-variable circuit array
$C^X$, with entries in the field $\mathbb{Q}(X)$ of rational functions over $\mathbb{Q}$, to integer
row indices by $C_{i,j} = C^X_{i,j}$ for $i \ge 0$ and $C_{i,j} = 1$ for $i < 0$. For an integer
$i$ and a natural number $j$, let $\tau_{i,j}$ be the triangle with left edge $C_{i,j}$ and right
and base edges $C_{i-1,j}$. Let $\mathcal{P}$, $\mathcal{L}$ and $\mathcal{R}$ be the
left-perimeter, left-edge and right-edge functions of the reduction. Then:
(i) $C_{2(c-1),c} = \mathcal{P}(\tau_{2(c-2),c-1}, \tau_{2(c-2),c-1})$ for every natural number
$c \ge 2$;
(ii) $C_{2(c-1),j} = \mathcal{L}(\tau_{2(c-1),j-1}, \tau_{2c-4,j-1}, \tau_{2c-4,j-1})$ for all
natural numbers $c$, $j$ with $2 \le c < j$;
(iii) $C_{2c-3,j} = \mathcal{R}(\tau_{2c-4,j-1}, \tau_{2c-6,j-1}, \tau_{2c-6,j-1})$ for all
natural numbers $c$, $j$ with $2 \le c \le j$;
(iv) $C^X_{0,1} = (X - 3)/X$.

Here $\mathcal{R}$ is the right-edge function of the reduction algorithm, not the misprinted
display (2.4), and the printed $C_{2(c-1-4),j-1}$ in (iii) is read as $C_{2(c-1)-4,j-1}$.

## Sources

- Emily J. Evans and Russell Jay Hendel, *Recursions and Characteristic Polynomials of the Rows of the Circuit Array*, Fibonacci Quarterly 62 (2024), Article 62-4/hendel08232024rev2, Proposition 4.1 (`fq-2024-hendel08232024rev2-prop-4.1`).
