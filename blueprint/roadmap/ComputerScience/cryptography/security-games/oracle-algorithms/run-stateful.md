# Run Stateful

Run an oracle computation against a **stateful deterministic oracle** whose state is the query
counter: the query `x` asked when the counter is `i` is answered by `s i x`. Starting from counter
`i`, `runStateful s i c` returns the output and the transcript of `(query, answer)` pairs; this is
how a stateful signer (Katz and Lindell, Section 12.6) is run in a forgery experiment. Each answer
and the recursive run are computed once, so a run costs work linear in the number of queries.

Relation to `runState` (`CSLibExt.Crypto.Framework.LazySampling`, and the function of the same
name in the open random-oracle pull request): `runState` runs against a randomized oracle with an
arbitrary state and returns a `PMF` of the output and final state, while `runStateful` is
deterministic, fixes the state to the counter and returns the transcript. Whoever unifies the
stateful runners in Wave 3 can derive this one as the deterministic, transcript-logging case.
