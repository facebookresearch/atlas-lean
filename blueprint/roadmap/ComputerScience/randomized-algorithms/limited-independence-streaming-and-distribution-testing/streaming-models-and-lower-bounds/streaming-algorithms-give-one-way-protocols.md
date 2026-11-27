# Streaming algorithms give one-way communication protocols

Let a one-pass streaming algorithm use at most $b$ bits of memory, and suppose that for maps $u, v$ from Alice's and Bob's inputs to streams, its answer on the concatenation $u(x)\, v(y)$ determines $f(x, y)$. Then $f$ has a one-way deterministic protocol of cost at most $b + 1$: Alice runs the algorithm on $u(x)$ and sends the memory state, Bob continues on $v(y)$ and announces the answer. For randomized streaming algorithms with error $\varepsilon$ the same gives a public-coin protocol with error $\varepsilon$. A $p$-pass algorithm gives a protocol with $2p - 1$ messages of $b$ bits; a nondeterministic multi-pass algorithm gives a rectangle cover with $2^{O(pb)}$ rectangles.

## Proof sketch

Simulate the streaming algorithm across the split of the stream, passing the memory state at each boundary crossing; nondeterministic choices become guesses.

## Depends on

- [Randomized streaming algorithm with $s$ bits of memory](../../frequency-moments-of-data-streams/streaming-algorithm.md)
- [Deterministic two-party protocol](../../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/protocol.md)
- [Public-coin randomized protocol](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/public-coin-protocol.md)

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The Space Complexity of Approximating the Frequency Moments", Journal of Computer and System Sciences 58(1), 1999.
- A. Chakrabarti, "Data Stream Algorithms: Lecture Notes", Dartmouth College, 2020.
