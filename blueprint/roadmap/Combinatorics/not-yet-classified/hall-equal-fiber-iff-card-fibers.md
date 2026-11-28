# Hall's condition for the equal-label relation

For labelings `f : A → K` and
`g : B → K` of finite types, every `S : Finset A` has at least `#S` elements `b` with
`g b = f a` for some `a ∈ S` if and only if every fiber of `f` has at most as many elements as the
corresponding fiber of `g`.

This is the Hall condition of `Fintype.all_card_le_filter_rel_iff_exists_injective` for the
relation `fun a b => f a = g b`; a matching for it is a label-preserving injection.
