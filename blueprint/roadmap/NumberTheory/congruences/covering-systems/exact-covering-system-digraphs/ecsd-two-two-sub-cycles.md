# Cycles of the digraph $G(2n, 2n - a)$

For an integer $b$ write $G_b$ for the digraph
$G(2n, 2n - b)$ on $\mathbb{Z}$, with an edge $m \to 2m$ and an edge $m \to 2m - b$ for every
integer $m$. Let $a$ be an odd natural number, write $x \bmod a$ for the residue of $x$ in
$\{0, \dots, a - 1\}$, and write $\operatorname{ord}(2, q)$ for the multiplicative order of $2$
modulo $q$. Then (i) $G_a$ has a loop at $m$ if and only if $m = 0$ or $m = a$; (ii) $G_a$ has a
directed walk of positive length from $m$ back to $m$ if and only if $0 \le m \le a$; (iii) the
list $(2^k \bmod a)_{0 \le k < \operatorname{ord}(2, a)}$ is a cycle of $G_a$; for every integer
$b$ with $1 \le b < a$ the list $(b 2^k \bmod a)_{0 \le k < \operatorname{ord}(2, a/\gcd(a, b))}$
is a cycle of $G_a$; and every cycle of $G_a$ with more than one vertex is a rotation of one of
these lists for some integer $b$ with $1 \le b < a$; (iv) for all natural numbers $t$ and $a'$
with $a = t a'$, a list $(c_1, \dots, c_s)$ of integers is a cycle of $G_{a'}$ if and only if
$(t c_1, \dots, t c_s)$ is a cycle of $G_a$.

## Sources

- Dana Neidmann, *Exact Covering System Digraphs of Degree 2 and Non-Standard Binary Representations of Integers*, INTEGERS 26 (2026), Article A107, Theorem 6.
