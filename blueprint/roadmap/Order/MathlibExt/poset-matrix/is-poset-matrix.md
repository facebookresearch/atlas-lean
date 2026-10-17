---
article_id: af_5f92703e83401758c1e5903d
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsPosetMatrix
---

# Is Poset Matrix

Upper-triangular `(0, 1)`-poset matrix (concept `jis_sem_b6df1a00e0451f0892d6d4dd`):
a square Boolean matrix `M` over `Fin n` with false entries strictly below the
main diagonal (D2), true entries on the main diagonal (D3), and transitivity of
the true entries (D4): `M i j = true` and `M j k = true` imply `M i k = true`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Order.PosetMatrix](../../../../sources/v2/MathlibExt.md)
- JIS `mohammad3.tex`, lines 171–176, SHA-256 `839f29b85b01af033998ae2ca01fb12acb8b055b72ed095859474eb3f746a2b8`.
