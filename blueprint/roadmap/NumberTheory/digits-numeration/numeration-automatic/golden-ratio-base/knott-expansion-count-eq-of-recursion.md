# Recursion for the number of Knott expansions

Let $\varphi$ be the golden ratio, let
$N \ge 2$ and $n$ be natural numbers, and let $p_0, \dots, p_n$ be integers with
$p_{k+1} \ge p_k + 2$ for all $k < n$ and $\sum_{k=0}^{n} \varphi^{p_k} = N$. Thus $N$ has the
base phi expansion $10^{s_n} \cdots 10^{s_1} 1$ with digits $1$ at positions $p_0 < \dots < p_n$,
where $s_k = p_k - p_{k-1} - 1$ for $1 \le k \le n$. Let $r_0, r_1, \dots$ be integers with
$r_0 = 1$; if $n \ge 1$, let $r_1 = s_1/2 + 1$ when $s_1$ is even and $r_1 = (s_1 + 1)/2 + 1$
when $s_1$ is odd; and for $2 \le k \le n$, let $r_k = (s_k/2 + 1)\, r_{k-1}$ when $s_k$ is even
and $r_k = ((s_k + 1)/2 + 1)\, r_{k-1} - r_{k-2}$ when $s_k$ is odd. Then the number of Knott
expansions of $N$ is $r_n$.

## Sources

- Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 2.3 (`fq-2024-dekking11102023-thm-2.3`).
