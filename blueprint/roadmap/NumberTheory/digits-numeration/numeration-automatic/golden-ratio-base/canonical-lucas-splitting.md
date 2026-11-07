# Canonical splitting of a Lucas interval

Let $L_j$ be the $j$-th Lucas number
($L_0 = 2$, $L_1 = 1$, $L_{j+2} = L_{j+1} + L_j$). For a natural number $m$, the canonical
splitting of the Lucas interval $\Lambda_m$ is the list of pairs $(k, t)$ of natural numbers
defined by recursion on $m$: for $m \le 5$ it is the one-pair list $[(m, 0)]$, and for $m \ge 6$
it is the concatenation, in this order, of the canonical splitting of $\Lambda_{m-2}$ with
$L_{m-1}$ added to the second coordinate of each pair, the canonical splitting of
$\Lambda_{m-3}$ with $L_m$ added to the second coordinate of each pair, and the canonical
splitting of $\Lambda_{m-2}$ with $L_m$ added to the second coordinate of each pair.

Here $\Lambda_{2n} = [L_{2n}, L_{2n+1}]$ and $\Lambda_{2n+1} = [L_{2n+1} + 1, L_{2n+2} - 1]$, and a
pair $(k, t)$ stands for the translate $\Lambda_k + t$. The recursion follows the second
Recursive Structure Theorem
$\Lambda_m = (\Lambda_{m-2} + L_{m-1}) \cup (\Lambda_{m-3} + L_m) \cup (\Lambda_{m-2} + L_m)$
(the paper's splittings of $\Lambda_6, \Lambda_7, \Lambda_8$, "continuing in this fashion").
That for $m \ge 3$ the result splits $\Lambda_m$ into adjacent translates of $\Lambda_3$,
$\Lambda_4$ and $\Lambda_5$ is the paper's Theorem 4. Only $m \ge 3$ is used.

## Sources

- F. Michel Dekking, *The Structure of Base Phi Expansions*, INTEGERS 24 (2024), Article A24, Section 4 (canonical splitting).
