# Recursive structure of the negative parts of base phi expansions

Let $n \ge 1$, let $L_k$
be the Lucas numbers, and for $j \ge 0$ let $\Lambda_{2j}$ be the set of natural numbers in
$[L_{2j}, L_{2j+1}]$ and $\Lambda_{2j+1}$ the set of natural numbers in
$[L_{2j+1} + 1, L_{2j+2} - 1]$. Let $T$ be a base phi expansion of a natural number $M$ and $S$ a
base phi expansion of a natural number $N$, both given as sets of positions of digits $1$. Write
$S^- = \{i \in S : i < 0\}$ and, for an integer $a$, $T_a = \{i \in T : a \le i < 0\}$. Then:
(A)(a) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n}$, then $S^- = T_{2-2n} \cup \{1-2n, -2n-2\}$;
(A)(b) if $M \in \Lambda_{2n-2}$ and $N = M + L_{2n+1}$, then $S^- = T_{4-2n} \cup \{1-2n, -2n-2\}$;
(A)(c) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+1}$, then $S^- = T_{2-2n} \cup \{-2n-2\}$;
(B)(a) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+1}$, then $S^- = T_{2-2n} \cup \{-2n-2\}$;
(B)(b) if $M \in \Lambda_{2n-1}$ and $N = M + L_{2n+2}$, then $S^- = T_{2-2n} \cup \{-2n, -2n-2\}$;
(B)(c) if $M \in \Lambda_{2n}$ and $N = M + L_{2n+2}$, then $S^- = T_{2-2n} \cup \{-2n, -2n-2\}$.

These are the paper's identities for the words $\gamma^-(N)$, the negative part of the expansion of
$N$ with its final digits $01$ removed; for example (A)(a) is
$\gamma^-(M + L_{2n}) = \gamma^-(M)\,10$. In (B)(c) the source writes $\gamma^-(N - L_{2n+1})$ for
$N \in \Lambda_{2n} + L_{2n+2}$; the shift $L_{2n+2}$ is used here, since as printed $n = 1$ and
$N = 10$ give $\gamma^-(6)\,01 = 0001$ while $\gamma^-(10) = 01$.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Theorem 10.
