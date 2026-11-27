# Query bound of the MAC forgers

For a chosen-ciphertext adversary making at most $q$ queries, every MAC forger built from it, for any
tape length and any guessed index, makes at most $q + 1$ tagging queries: one per encryption query of
the adversary and one to tag the challenge. So the forgers are admissible for $(q + 1)$-query MAC
security.
