# Bounded-coin trapdoor function scheme

Setup, key generation and domain sampling are each performed by a uniform polynomial-time algorithm using a fresh string of fair bits whose length is a fixed polynomial in the positive security parameter. Setup realizes the specified setup law, and at every possible setup output, key generation realizes the conditional joint key law. At each generated public context (a system parameter that setup can produce and a public key occurring in a matching generated pair), the domain is nonempty and the domain sampler is exactly uniform on it.

The two membership tests and the public and secret maps run in polynomial time on all inputs. The tests must decide membership correctly for every candidate word at each generated public context; enumeration is not required. One polynomial bounds the lengths of the system parameter, both keys and all words in either space over all generated pairs. The matching maps satisfy the trapdoor correctness law at every such pair.

This is the bounded-coin convention, not the [variable-time convention](variable-time-trapdoor-function-scheme.md) of a negligible running-time overrun.
