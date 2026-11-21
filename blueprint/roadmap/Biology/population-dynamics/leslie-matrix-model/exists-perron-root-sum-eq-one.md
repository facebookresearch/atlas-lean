# Perron root of a Leslie matrix

Let $L$ be the Leslie matrix of $n \ge 1$ age classes with fertilities $f_0, \dots, f_{n-1}$ and
survival probabilities $s_0, \dots, s_{n-1}$, and suppose that $L$ is irreducible: its entries are
nonnegative, and for all age classes $i$ and $j$ (including $i = j$) there is a sequence
$i = i_0, i_1, \dots, i_k = j$ with $k \ge 1$ and $L_{i_{t-1} i_t} > 0$ for $t = 1, \dots, k$. Then there
are a real $r > 0$ and a vector $v \in \mathbb{R}^n$ with positive entries such that $Lv = rv$, every
complex eigenvalue $\mu$ of $L$ satisfies $|\mu| \le r$, and
$$\sum_i \frac{f_i l_i}{r^{i+1}} = 1,$$
the discrete Euler–Lotka equation, where $l_i = s_0 s_1 \cdots s_{i-1}$ is the survivorship, with
$l_0 = 1$.
