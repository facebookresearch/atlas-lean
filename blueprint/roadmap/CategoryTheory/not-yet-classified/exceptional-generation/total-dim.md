# Total Dim

The sum `∑ᶠ n, dim_k Hom(G⟦n⟧, X)`. It is the total dimension of the graded `Hom` when
`FinTot k G X` holds, and it is only used under that hypothesis: otherwise `Module.finrank`
of an infinite-dimensional piece and the `finsum` of an infinite support are `0`.
