# Hook tableau counts as differences of hump counts

For natural numbers $m$ and $j$, let
$\mathrm{SYT}_j(2,1;m)$ be the number of standard Young tableaux of order $m$ in the
$(2,1)$-hook whose first row is longer than its second row by exactly $j$, and let $H_{m,j}$ be
the number of Motzkin paths of length $m$ with one distinguished hump of height $j$ (a hump is
an up step followed by flat steps and then a down step; its height is the height reached by the
up step). For natural numbers $n$ and $k$ with $1 \le k \le \lfloor n/2 \rfloor$,

$$
\mathrm{SYT}_{2k-1}(2,1;n+1) + \mathrm{SYT}_{2k-1}(2,1;n) = H_{n+1,k} - H_{n,k},
$$

where the subtraction is taken in the integers.

## Sources

- Xiaomei Chen, *Humps in Motzkin Paths and Standard Young Tableaux in a (2,1)-Hook*, Journal of Integer Sequences 28 (2025), Article 25.8.1, Corollary 10 (`jis-2025-25.8.1-cor-10`).
