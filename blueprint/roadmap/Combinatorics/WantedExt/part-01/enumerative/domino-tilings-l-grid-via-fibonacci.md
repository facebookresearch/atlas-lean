---
article_id: af_cb29c4c97789b524bbbbf068
declaration: theorem
origin: cited
statement: formalized
lean: MetaMathlibExt.domino_tilings_L_grid_via_fibonacci
---

# LGrid Domino Tilings Wanted

The Fibonacci formula for the number of domino tilings of the L-grid, together
with its specialization and Cassini-type identity.

With `f_0 = 0, f_1 = 1` (`Nat.fib`), the tiling count `L` is unfolded as the
Fibonacci expression `f_{n+1} f_m + f_n f_{m+1}`, so the first two conjuncts
are definitional; the substantive content is the Cassini-type identity
`L_{n,n-1}^2 = L_{n,n} L_{n-1,n-1} + 1` (checked for `2 ≤ n ≤ 11`).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Combinatorics.Enumerative.LGridDominoTilingsWanted](../../../../../sources/v2/WantedExt.md)
- Roberto Tauraso, "A New Domino Tiling Sequence," Journal of Integer Sequences 7 (2004), Article 04.2.3, Lemma (Section 2, equations Lformula and Lcassini), lines 200–221, https://cs.uwaterloo.ca/journals/JIS/VOL7/Tauraso/tauraso3.tex
