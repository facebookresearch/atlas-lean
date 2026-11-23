# The Cochran–Armitage trend test is asymptotically `χ²₁`

Subjects `S m = (G m, Y m)`
(genotype class, case status) are i.i.d. (*multinomial sampling* of the `2 × 3` table). Under
the null `G 0 ⟂ Y 0`, with case probability `p = P(Y 0 = true) ∈ (0, 1)` and positive genotype
score variance (at least two genotype classes of positive probability), the trend statistic of
the first `N` subjects converges in distribution, as `N → ∞`, to `χ²₁`.

All three null parameters (`p` and two genotype frequencies) are fitted from the data inside
`caStat`; the limit still has one degree of freedom.
