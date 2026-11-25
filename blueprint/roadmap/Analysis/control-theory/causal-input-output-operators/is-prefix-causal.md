# Prefix-causal operators

A bounded operator `G` is **prefix causal** with respect to a
filtration `P` of bounded projections when every prefix of the output
of `G` depends only on the same prefix of the input: `P t ∘ G` never
reads past `P t`, i.e. `P t ∘L G = P t ∘L G ∘L P t` for all `t`. This
is a prefix law, not a commutation law: the unit delay is prefix
causal but does not commute with the `P t`.
