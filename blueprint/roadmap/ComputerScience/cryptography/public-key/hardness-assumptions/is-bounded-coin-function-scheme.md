# Bounded-coin trapdoor function scheme

Setup, conditional key generation and domain sampling are each realized by a uniform polynomial-time algorithm applied to a fresh string of fair bits. Its length is a fixed polynomial in the positive security parameter, and the required laws are exact, including the uniform law on the nonempty domain. Both public-key-indexed spaces have uniform polynomial-time membership tests; enumeration is not required. The public and secret maps are polynomial-time. One polynomial bounds the lengths of every generated system parameter, both keys and all words in either space. Correctness holds at every matching pair.

This is the bounded-coin convention, not the [variable-time convention](variable-time-trapdoor-function-scheme.md) of a negligible running-time overrun.
