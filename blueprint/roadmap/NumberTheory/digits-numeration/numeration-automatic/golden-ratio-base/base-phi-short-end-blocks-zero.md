# End blocks of length at most three ending in $0$

Let $\varphi$ be the golden ratio.
For integers $p, q, r$ let $V(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 1\}$ and
$V_0(p, q, r) = \{p \lfloor n\varphi \rfloor + qn + r : n \ge 0\}$. For a word $w$ of length $\ell$
let $R_w$ be the set of natural numbers having a base phi expansion whose digits
$d_{\ell-1} \cdots d_0$ at positions $\ell - 1, \dots, 0$ spell $w$. Then for every natural number
$N \ge 1$: $N \in R_0$ if and only if $N \in V(-1, 3, 0)$; $N \in R_{00}$ if and only if
$N \in V_0(1, 2, 0) \cup V(3, 1, 1)$; $N \in R_{10}$ if and only if $N \in V(1, 2, -1)$;
$N \in R_{010}$ if and only if $N \in V(1, 2, -1)$; $N \in R_{000}$ if and only if
$N \in V_0(4, 3, 0) \cup V(3, 1, 1)$; and $N \in R_{100}$ if and only if $N \in V(3, 1, -1)$.
Moreover $V_0(1, 2, 0)$ and $V_0(4, 3, 0)$ are each disjoint from $V(3, 1, 1)$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Proposition 2.
