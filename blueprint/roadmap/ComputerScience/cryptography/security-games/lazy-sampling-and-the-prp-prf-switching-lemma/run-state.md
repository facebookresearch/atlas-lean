# Run State

Run an oracle computation against a **stateful randomized oracle** `O`, which answers the
query `x` in state `s` by sampling an answer and a new state from `O s x`. This is oracle access
to a stateful algorithm, e.g. a lazily sampled random oracle (Katz and Lindell, Section 5.5.1).
The open random-oracle pull request defines the same function as `Cslib.Crypto.Framework.runState`;
Wave 3 keeps one of the two.
