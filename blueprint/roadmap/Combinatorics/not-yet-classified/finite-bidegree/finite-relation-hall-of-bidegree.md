# Hall's condition from degree bounds

If every source is related to at least `degree`
targets and every target to at most `degree` sources, with `0 < degree`, then every finite set of
sources is related to at least as many targets. This is the double-counting step behind König's
theorem that regular bipartite graphs have perfect matchings (D. König, 1916). See also
`Fintype.all_card_le_filter_rel_iff_exists_injective` (Hall's marriage theorem) to turn the
conclusion into a matching.
