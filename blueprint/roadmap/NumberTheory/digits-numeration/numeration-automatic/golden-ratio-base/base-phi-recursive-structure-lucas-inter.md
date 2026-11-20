# Recursive structure of base phi expansions on Lucas intervals

Let $n \ge 1$, let $L_k$ be
the Lucas numbers, and for $j \ge 0$ let $\Lambda_{2j}$ be the set of natural numbers in
$[L_{2j}, L_{2j+1}]$ and $\Lambda_{2j+1}$ the set of natural numbers in
$[L_{2j+1} + 1, L_{2j+2} - 1]$. Let $T$ be a base phi expansion of a natural number $M$ and $S$ a
base phi expansion of a natural number $N$, both given as sets of positions of digits $1$. Then:
(A)(a) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n}$, then $2n-1 \in T$, $2n-2 \notin T$,
$1-2n \notin T$, $-2n \in T$ and $S = (T \setminus \{2n-1, -2n\}) \cup \{2n+1, 1-2n, -2n-2\}$;
(A)(b) if $M \in \Lambda_{2n-2}$ and $N = M + L_{2n+1}$, then $3-2n \notin T$, $2-2n \in T$ and
$S = (T \setminus \{2-2n\}) \cup \{2n+1, 1-2n, -2n-2\}$;
(A)(c) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+1}$, then $2n-1 \in T$, $1-2n \notin T$,
$-2n \in T$ and $S = (T \setminus \{-2n\}) \cup \{2n+1, -2n-2\}$;
(B)(a) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+1}$, then $2n \in T$, $2n-1 \notin T$,
$1-2n \notin T$, $-2n \in T$ and $S = (T \setminus \{2n, -2n\}) \cup \{2n+2, -2n-2\}$;
(B)(b) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+2}$, then $S = T \cup \{2n+2, -2n-2\}$;
(B)(c) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+2}$, then $S = T \cup \{2n+2, -2n-2\}$.

In the paper's word notation, where $\beta(M)$ is the expansion of $M$ written as a word of digits
(with $\cdot$ between positions $0$ and $-1$) and $(10)^{-1}$, $(01)^{-1}$ cancel a leading $10$
and a trailing $01$, (A)(a) is
$\beta(M + L_{2n}) = 1000\,(10)^{-1}\,\beta(M)\,(01)^{-1}\,1001$ and (B)(b) is
$\beta(M + L_{2n+2}) = 100\,\beta(M)\,01$; the digit conditions on $T$ make the cancellations
$(10)^{-1}$ and $(01)^{-1}$ valid. In (B)(c) the source writes $\beta(N - L_{2n+1})$ for
$N \in \Lambda_{2n} + L_{2n+2}$; the shift $L_{2n+2}$ is used here, since as printed $n = 1$ and
$N = 10$ give $10\,\beta(6)\,01 = 101010 \cdot 000101$, which is not $\beta(10) = 10100 \cdot 0101$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 3.
