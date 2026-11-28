# Mfm Is ABSeparator

`S` separates `A` from `B` in `G`: every walk from a vertex of `A` to a vertex of `B` visits a
vertex of `S`. This is the walk-hitting predicate
`MathlibExt.Combinatorics.SimpleGraph.SeparatorAPI.SeparatesAB G ↑A ↑B S` with finite terminal
sets. Walk supports contain their endpoints, so vertices of `A ∩ B` must lie in `S` (take the
trivial walk), and `S` may meet `A ∪ B`, unlike `SeparatorAPI.IsSeparatorAB`.
