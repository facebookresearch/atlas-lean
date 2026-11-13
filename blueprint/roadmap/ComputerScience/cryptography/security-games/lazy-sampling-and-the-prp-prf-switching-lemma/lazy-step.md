# Lazy Step

One step of a **lazily sampled** oracle with table `T`: a recorded query is answered from the
table; a fresh query `x` is answered by a sample `y` of `fresh T x`, and `x ↦ y` is recorded
(Katz and Lindell, Section 5.5.1: the oracle "keeps a table" and answers a new query with a fresh
random value).
