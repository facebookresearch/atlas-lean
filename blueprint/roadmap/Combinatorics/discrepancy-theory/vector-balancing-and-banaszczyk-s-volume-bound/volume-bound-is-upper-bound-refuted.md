# Banaszczyk's volume bound is not an upper bound for vector balancing

There are no real
constants $C$ and $c$ such that for every natural number $d \ge 2$, all norms $X$ and $Y$ on
$\mathbb{R}^d$, every natural number $n$ and all vectors $v_1, \dots, v_n \in \mathbb{R}^d$ with
$X(v_i) \le 1$ for every $i$, there are signs $\varepsilon_1, \dots, \varepsilon_n \in \{1, -1\}$
such that $Y(\varepsilon_1 v_1 + \dots + \varepsilon_n v_n)$ is at most
$C (\log d)^c \sqrt{d} \, (\mathrm{vol}(B_X) / \mathrm{vol}(B_Y))^{1/d}$, where
$B_X = \{x : X(x) \le 1\}$ and $B_Y = \{x : Y(x) \le 1\}$ are the closed unit balls and
$\mathrm{vol}$ is Lebesgue measure.

S. Nikolov's remark on the problem gives the counterexample $X = Y = \ell_1^d$ with the standard
basis vectors $e_1, \dots, e_d$: the volume bound is $\sqrt{d}$, while every choice of signs gives
$\|\pm e_1 \pm \dots \pm e_d\|_1 = d$, and a factor $\sqrt{d}$ is not polylogarithmic in $d$.

## Sources

- AimPL: Hereditary discrepancy and factorization norms, Section 1, Problem 1.5 (Vector balancing), http://aimpl.org/hereddiscrep/1/; resolution: AimPL: Hereditary discrepancy and factorization norms, remark by S. Nikolov to Problem 1.5, remark: 'In fact, this lower bound can be too small by a factor of √d, for example when X = Y = ℓ_1^d' (for X = Y the volume bound is √d, while for the standard basis e_1, ..., e_d every signing has ‖∑ ±e_i‖_1 = d), http://aimpl.org/hereddiscrep/1/.
