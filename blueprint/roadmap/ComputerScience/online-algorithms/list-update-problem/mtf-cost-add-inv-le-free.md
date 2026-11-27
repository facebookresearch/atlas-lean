# Amortized bound for move-to-front over a request sequence, with free exchanges

Let $M$ be
a list without duplicates, $\sigma$ a sequence of $m$ requests, each an item of $M$, $L_0, L_1,
\dots$ lists that are each a rearrangement of $M$, and $J_0, J_1, \dots$ natural numbers.
Accessing the item at position $i$ of a list, counting from $1$, costs $i$. Let $C$ be the total
access cost of move-to-front on $\sigma$ starting from $M$, $F$ the list it ends with, and $D$
the cost on $\sigma$ of the offline algorithm with free exchanges that serves the $t$-th request
(counting from $0$) with list $L_t$, paying its access cost, then moves the accessed item forward
for free so that exactly $J_t$ items precede it (no move if at most $J_t$ items already precede
it), and finally rearranges the resulting list into $L_{t+1}$, paying one for each pair of items
whose relative order changes. Writing $\mathrm{inv}(N, K)$ for the number of inversions of $K$
against $N$,

$$C + \mathrm{inv}(F, L_m) + m \le 2D + \mathrm{inv}(M, L_0).$$
