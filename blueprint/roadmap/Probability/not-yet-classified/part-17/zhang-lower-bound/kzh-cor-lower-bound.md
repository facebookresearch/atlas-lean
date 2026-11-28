# Harris's theorem

**Harris's theorem** `θ(1/2) = 0` on `ℤ²` via Zhang's argument (Harris, 1960; Zhang, 1988,
unpublished; see Grimmett, *Percolation*, 1999, §11.3), conditional form.

The content is carried by `hZhangUnion` (if `θ(1/2) > 0`, then `ℙ(A n ∪ B n) → 1`) and by the
self-dual dichotomy `hdich` for `A n`; both are hypotheses, see the module docstring. The
assumption `BoxCrossingProperty halfMeasure 2` is only passed on to `hZhangUnion`.
