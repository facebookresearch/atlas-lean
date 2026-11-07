# Recursion for the number of natural expansions

Let $N$ and $n$ be natural numbers and
let $p_0, \dots, p_n$ be integers with $p_k + 2 \le p_{k+1}$ for $k < n$ such that the base phi
expansion with digits $1$ at positions $p_0, \dots, p_n$ represents $N$. Put
$s_k = p_k - p_{k-1} - 1$ for $1 \le k \le n$. Let $r_0, r_1, \dots$ be integers with
$r_0 = 1$ such that, if $n \ge 1$, $2 r_1 = s_1 + 2$ when $s_1$ is even and $2 r_1 = s_1 + 1$
when $s_1$ is odd, and for $2 \le k \le n$, $2 r_k = (s_k + 2) r_{k-1}$ when $s_k$ is even and
$2 r_k = (s_k + 3) r_{k-1} - 2 r_{k-2}$ when $s_k$ is odd. Then the number
$\mathrm{Tot}_\nu(N)$ of natural base phi expansions of $N$ equals $r_n$.

Compared with the recursion for the number of Knott expansions, only the value of $r_1$ for odd
$s_1$ differs, and $N \ge 2$ is not assumed.

## Sources

- Michel Dekking and Ad van Loon, *Counting Base Phi Representations*, Fibonacci Quarterly 62 (2024), Article 62-2/dekking11102023, Theorem 4.1 (`fq-2024-dekking11102023-thm-4.1`).
