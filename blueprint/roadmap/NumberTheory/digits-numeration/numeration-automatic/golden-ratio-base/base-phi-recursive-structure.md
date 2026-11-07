# Recursive structure theorem for base phi expansions, part (A)

Let $n \ge 2$ and let $L_j$
be the Lucas numbers; $k$ denotes a natural number, and base phi expansions are given as sets of
positions of digits $1$.
(I) If $1 \le k \le L_{2n-2} - 1$, $T$ is a base phi expansion of $L_{2n-1} + k$ and $S$ is a base
phi expansion of $L_{2n+1} + k$, then $2n-1 \in T$, $2n-2 \notin T$, $1-2n \notin T$, $-2n \in T$
and $S = (T \setminus \{2n-1, -2n\}) \cup \{2n+1, 1-2n, -2n-2\}$.
(K) If $1 \le k \le L_{2n-2} - 1$, $T$ is a base phi expansion of $L_{2n-1} + k$ and $S$ is a base
phi expansion of $L_{2n+1} + L_{2n-1} + k$, then $2n-1 \in T$, $2n-2 \notin T$, $1-2n \notin T$,
$-2n \in T$ and $S = (T \setminus \{-2n\}) \cup \{2n+1, -2n-2\}$.
(J) If $0 \le k \le L_{2n-3}$, $T$ is a base phi expansion of $L_{2n-2} + k$ and $S$ is a base phi
expansion of $L_{2n+1} + L_{2n-2} + k$, then $2n-2 \in T$, $2n-3 \notin T$, $3-2n \notin T$,
$2-2n \in T$ and $S = (T \setminus \{2-2n\}) \cup \{2n+1, 1-2n, -2n-2\}$.

In the paper's word notation, where $\beta(M)$ is the expansion of $M$ written as a word of digits
(with $\cdot$ between positions $0$ and $-1$) and $(10)^{-1}$, $(01)^{-1}$ cancel a leading $10$
and a trailing $01$, these are
$\beta(L_{2n+1}+k) = 1000\,(10)^{-1}\,\beta(L_{2n-1}+k)\,(01)^{-1}\,1001$,
$\beta(L_{2n+1}+L_{2n-1}+k) = 1010\,(10)^{-1}\,\beta(L_{2n-1}+k)\,(01)^{-1}\,0001$ and
$\beta(L_{2n+1}+L_{2n-2}+k) = 10010\,(10)^{-1}\,\beta(L_{2n-2}+k)\,(01)^{-1}\,001001$. The
source's ranges $k \le L_{2n} - 1$ for (I) and (K) and $k \le L_{2n-1}$ for (J) are too wide: for
$n = 2$ and $k = 3$, $\beta(L_3 + 3) = \beta(7) = 10000 \cdot 0001$ has no digit $1$ at
position $3$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 2 (`integers-2024-A24-thm-2`).
