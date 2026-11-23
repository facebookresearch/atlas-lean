# Law of total covariance for a nested finite population

**Law of total covariance for a nested finite population** (key lemma of the multilevel
Price equation). Individuals are the elements `⟨k, j⟩` of `Σ k, α k`: group `k : κ` has members
`j : α k`. All moments are population (not sample) moments with every individual weighted
equally, so group `k` has weight `q k = |α k| / |Σ k, α k|` (proportional to its size) and
group means `X k = 𝔼 j, x ⟨k, j⟩`, `Y k = 𝔼 j, y ⟨k, j⟩`. Then the population covariance of
`x` and `y` splits into the size-weighted covariance of the group means (between groups) plus
the size-weighted mean of the within-group population covariances:

`Cov(x, y) = ∑ k, q k (X k - ∑ l, q l X l) (Y k - ∑ l, q l Y l)
  + ∑ k, q k 𝔼 j, (x ⟨k, j⟩ - X k) (y ⟨k, j⟩ - Y k)`.

No hypothesis is needed: an empty group has weight `0`, and an empty population makes both
sides `0`.
