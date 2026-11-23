# Number of hash sequences that leave a given cell empty

Let $1 \le n \le N$ and let $c$ be a cell of a cyclic table of $N$ cells. Exactly
$(N - n)\,N^{n-1}$ of the $N^n$ hash sequences of $n$ items leave $c$ empty after linear probing,
a fraction $(N - n)/N$. For $N = 3$ and $n = 2$, three of the nine sequences leave cell $0$ empty.

Knuth's 1998 paper states it for cell $0$: "exactly $(m - n)/m$ of them will be confined". With
$N = n' + 1$ cells and $c$ the last cell, a sequence leaving $c$ empty never wraps around, so this
is also Knuth's 1963 count of [non-overflow sequences on $n'$ cells](card-lin-success.md), which
also follows from Pollak's count of partial parking functions.

## Informally uses

- [Rotational symmetry of linear probing](mul-card-not-mem-occupancy.md): the identity divided by
  $N$.

## Sources

- D. E. Knuth, "Linear probing and graphs", *Algorithmica* 22 (1998) 561–568, Section 1;
  arXiv:cs/9801103.
