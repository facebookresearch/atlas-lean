# Endpoint positions of an axial-member table

Let `J` be a set of joints with positions `r : J → ℝ²` and `M` a set of members, member `e` joining
the joints `a(e)` and `b(e)`. The endpoints of the table are indexed by pairs `(e, s)` with `e ∈ M`
and `s` a Boolean flag: the position of `(e, false)` is `r(a(e))` and that of `(e, true)` is
`r(b(e))`. Indexing by pairs keeps parallel members, joining the same joints, as distinct entries.
