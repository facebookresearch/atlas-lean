# A fair-bit sampler

A fixed finite control and a fixed number of binary work tapes,
with the ordinary bounded-head read-only input and write-only output. The finite transition
table selects a single local action given the state, symbols under the heads and a fresh fair
bit. It may ignore that bit. There are no transition probabilities supplied by the caller.
