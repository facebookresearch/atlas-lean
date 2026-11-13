# Neighbor joining averages up to row shifts

Along every run of neighbor joining on a
symmetric dissimilarity `d` with zero diagonal there are weights `α s` (nonnegative, supported
on `s`, summing to `1`) and row terms `κ s` such that the cluster dissimilarity vanishes on the
diagonal and `D s t = ∑ x, ∑ y, α s x * α t y * d x y - κ s - κ t` for distinct current
clusters. Joining `a, b` takes `α (a ∪ b) = (α a + α b) / 2` and
`κ (a ∪ b) = (κ a + κ b + D a b) / 2`.
