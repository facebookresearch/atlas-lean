# Not balance Preserving Contraction

`BalancePreservingContraction` is false: it would force corner balance `-4` on the orbit around
the hole of `bpc_holeRing`, whose corner balance is positive. The induction below is the
`BalancePreservingContraction`-implies-`-4` argument, inlined so that no exported theorem assumes
the refuted hypothesis.
