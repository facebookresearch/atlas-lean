# Linear threshold function

A function $f : \{-1, 1\}^n \to \mathbb{R}$ is a linear
threshold function if there are reals $w_0, w_1, \dots, w_n$ such that for every
$x \in \{-1, 1\}^n$ we have $f(x) = \operatorname{sgn}(w_0 + w_1 x_1 + \dots + w_n x_n)$, where
$x_i \in \{-1, 1\}$ is the $i$-th coordinate of $x$, $\operatorname{sgn} z = 1$ for $z \ge 0$ and
$\operatorname{sgn} z = -1$ for $z < 0$.
