# Banaszczyk's volume bound as an upper bound for vector balancing (statement)

This is the
proposition that there are real constants $C$ and $c$ such that for every natural number $d \ge 2$,
all norms $X$ and $Y$ on $\mathbb{R}^d$, every natural number $n$ and all vectors
$v_1, \dots, v_n \in \mathbb{R}^d$ with $X(v_i) \le 1$ for every $i$, there are signs
$\varepsilon_1, \dots, \varepsilon_n \in \{1, -1\}$ such that
$Y(\varepsilon_1 v_1 + \dots + \varepsilon_n v_n)$ is at most
$C (\log d)^c \sqrt{d} \, (\mathrm{vol}(B_X) / \mathrm{vol}(B_Y))^{1/d}$, where
$B_X = \{x : X(x) \le 1\}$ and $B_Y = \{x : Y(x) \le 1\}$ are the closed unit balls and
$\mathrm{vol}$ is Lebesgue measure.

Banaszczyk proved that $\sqrt{d} \, (\mathrm{vol}(B_X) / \mathrm{vol}(B_Y))^{1/d}$ is a lower bound
for the vector balancing constant of $X$ and $Y$; the AimPL question asks whether it is also an
upper bound up to polylogarithmic factors in $d$.
