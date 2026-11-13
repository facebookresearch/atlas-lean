# Query bound of the MAC forgers

For a CCA adversary making at most `q` queries, every
`forger` (any tape length `n`, any guessed index `j`) makes at most `q + 1` tagging queries: one
per encryption query of the adversary, and one to tag the challenge. So the forgers of
`ccaAdvantage_le` are admissible for `(q + 1)`-query MAC security.
