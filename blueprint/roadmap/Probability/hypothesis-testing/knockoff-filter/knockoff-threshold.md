# Knockoff threshold

Let $p \in \mathbb{N}$, $c \in \mathbb{N}$ an offset ($c = 0$ for knockoff, $c = 1$ for knockoff+), $q \in \mathbb{R}$ a target level and $W = (W_1, \dots, W_p) \in \mathbb{R}^p$ statistics. The knockoff threshold is

$$T_c = \min\Big\{|W_j| : W_j \ne 0,\ \frac{c + \#\{i : W_i \le -|W_j|\}}{\max(\#\{i : W_i \ge |W_j|\}, 1)} \le q\Big\},$$

the least value $t = |W_j| > 0$ at which the estimated false discovery proportion is at most $q$, with $T_c = +\infty$ if there is none.

## Sources

- R. F. Barber and E. J. Candès, *Controlling the false discovery rate via knockoffs*, Ann. Statist. 43 (2015) 2055-2085, arXiv:1404.5609, equation (1.8) ($c = 0$) and Definition 2, equation (1.9) ($c = 1$).
