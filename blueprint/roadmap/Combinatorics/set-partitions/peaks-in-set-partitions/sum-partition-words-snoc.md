# Last-letter decomposition of a sum over partition words

For natural numbers $n,k$,
let $P_{n,k}$ be the surjective restricted-growth words of length $n$ on $k$ letters. For any
natural-valued weight $F$ on length-$(n+1)$ words on $\{0,\ldots,k\}$,

$$\sum_{w\in P_{n+1,k+1}} F(w) = \sum_{u\in P_{n,k}} F(uk)
  + \sum_{u\in P_{n,k+1}} \sum_{a=0}^k F(ua),$$

where $ua$ appends the letter $a$ to $u$. The first sum introduces the largest letter, and
the second extends a prefix that already uses every letter.
