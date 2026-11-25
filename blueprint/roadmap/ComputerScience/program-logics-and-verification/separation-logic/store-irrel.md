# Store-irrelevant heap assertions

A heap assertion $P$ is store-irrelevant when for all
stores $s, s'$ and every heap $h$, $P(s, h)$ implies $P(s', h)$; that is, whether $P$ holds
does not depend on the store.

The empty-heap and points-to assertions are store-irrelevant, and so is the separating
conjunction of two store-irrelevant assertions.
