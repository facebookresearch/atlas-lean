# Short end blocks

Let $\varphi$ be the golden ratio. For integers $p, q, r$ let
$V(p, q, r)$ be the set of the integers $p \lfloor n\varphi \rfloor + qn + r$ with $n \ge 1$, and
$V_0(p, q, r)$ the same set with $n \ge 0$. Then for every natural number $N \ge 1$:
some base phi expansion of $N$ has digit $1$ at position $0$ if and only if
$N \in V_0(1, 2, 1)$; some base phi expansion of $N$ has digits $1, 0$ at positions $1, 0$ if
and only if $N \in V(1, 2, -1)$; some base phi expansion of $N$ has digits $0, 0, 0$ at
positions $1, 0, -1$ if and only if $N \in V_0(1, 2, 0)$; and some base phi expansion of $N$
has digits $0, 0, 1$ at positions $1, 0, -1$ if and only if $N \in V(3, 1, 1)$.

In the paper's notation: $R_1 = V_0(1, 2, 1)$, $R_{10} = V(1, 2, -1)$,
$R_{00 \cdot 0} = V_0(1, 2, 0)$ and $R_{00 \cdot 1} = V(3, 1, 1)$, on the numbers $N \ge 1$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 6 (`integers-2024-A24-thm-6`).
