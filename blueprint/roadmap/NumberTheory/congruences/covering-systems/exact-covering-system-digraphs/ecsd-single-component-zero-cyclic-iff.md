# Degree-2 ECSDs with one component and $0$ on a cycle

Let $d_1, d_2 \in \{2, -2\}$ and let
$a_1, a_2$ be integers with $a_1 - a_2$ odd, excluding the case $d_1 = d_2 = -2$ with
$|a_1 - a_2| = 1$. Consider the exact covering system digraph $G(d_1 n + a_1, d_2 n + a_2)$, with
an edge $m \to d_i m + a_i$ for every integer $m$ and $i = 1, 2$. It has a single component (any
two integers are joined by a path in its underlying undirected graph) and a directed walk of
positive length from $0$ back to $0$ if and only if one of the following holds: $d_1 = 2$,
$d_2 = -2$, $a_1 = 0$ and $a_2 = \pm 1$; or $d_1 = -2$, $d_2 = 2$, $a_2 = 0$ and $a_1 = \pm 1$;
or $d_1 = d_2 = -2$, $|a_1 - a_2| = 3^m$ for some integer $m \ge 0$, neither $a_1$ nor $a_2$ is
divisible by $3$, and $\max(|a_1|, |a_2|) \le 2|a_1 - a_2| - 1$.

The excluded case behaves differently: $G(-2n + 1, -2n + 2)$ has a single component and the
cycle $(0, 1)$, although $\max(1, 2) = 2 > 2 \cdot 1 - 1$.

## Sources

- Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 17 (`integers-2026-A107-thm-17`).
