# Finite-support Marcus–Spielman–Srivastava bound

The proposition that the following holds
for every natural number $m$ and every finite index set $D$. Let $s_1, \dots, s_m$ be positive
integers, let $p_{i,a} \ge 0$ be reals and $v_{i,a} \in \mathbb{C}^D$ be vectors for
$1 \le i \le m$ and $1 \le a \le s_i$, and let $\eta \ge 0$ be real. Suppose that
$\sum_a p_{i,a} = 1$ for each $i$, that $\sum_i \sum_a p_{i,a} v_{i,a} v_{i,a}^* = \mathrm{Id}_D$,
and that $\sum_a p_{i,a} \|v_{i,a}\|^2 \le \eta$ for each $i$, where $\|v_{i,a}\|$ is the
Euclidean norm. Then there are choices $a_i \in \{1, \dots, s_i\}$ for $i = 1, \dots, m$ such
that $\left\|\sum_i v_{i,a_i} v_{i,a_i}^*\right\| \le (1 + \sqrt{\eta})^2$, where the norm of a
matrix is the operator norm.

In probabilistic terms, $p_{i,a}$ is the probability that an independent random vector $v_i$
takes the value $v_{i,a}$, and the conclusion is that some choice of values meets the bound.
