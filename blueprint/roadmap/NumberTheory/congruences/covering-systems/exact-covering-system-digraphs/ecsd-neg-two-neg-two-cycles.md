# Cycles of $G(-2n, -2n + a)$

Let $a$ be an odd natural number and $G = G(-2n, -2n + a)$.
A cycle of $G$ is a list $(c_1, \dots, c_t)$, $t \ge 1$, of distinct integers with edges
$c_1 \to c_2, \dots, c_{t-1} \to c_t$ and $c_t \to c_1$; a vertex is cyclic if it lies on a
cycle. For an integer $x$ let $\hat{x}$ be the representative of $x$ modulo $a$ in the interval
$(-a/3, 2a/3]$, and let $\operatorname{ord}_q(-2)$ be the multiplicative order of $-2$ modulo
$q$. Then:
(i) for every integer $m$, $G$ has a loop at $m$ iff $m = 0$ or $3m = a$;
(ii) an integer $m$ is cyclic iff $-a \le 3m \le 2a$;
(iii) if $3 \nmid a$, then $G$ has exactly $a$ cyclic vertices and each residue class modulo
$a$ contains exactly one of them; if $3 \mid a$, then $G$ has exactly $a + 1$ cyclic vertices,
each residue class modulo $a$ other than the class of $2a/3$ contains exactly one of them, and
the two-vertex list $(-a/3, 2a/3)$ is a cycle of $G$;
(iv) the list $(\widehat{(-2)^k})_{0 \le k < \operatorname{ord}_a(-2)}$ is a cycle of $G$, and
for every integer $b$ with $-a < 3b < 2a$, $b \ne 0$ and $3b \ne a$, so is the list
$(\widehat{b(-2)^k})_{0 \le k < \operatorname{ord}_{a/\gcd(a, b)}(-2)}$;
(v) if $a = t a'$ with $t, a' \in \mathbb{N}$, then a list $C$ of integers is a cycle of
$G(-2n, -2n + a')$ iff the list $tC$ obtained by multiplying every entry by $t$ is a cycle of
$G$.

The paper also assumes $a'$ odd in (v); this follows from $a$ odd.

## Sources

- Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 10 (`integers-2026-A107-thm-10`).
