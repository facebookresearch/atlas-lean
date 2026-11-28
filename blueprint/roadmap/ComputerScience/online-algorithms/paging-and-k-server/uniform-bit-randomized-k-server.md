# Uniform polynomial-bit randomized k-server policy

There exist one bit machine, natural $c>0,e\ge0$ and $C>0$ working for every $n\ge3$, $2\le k<n$, rational metric on $\{0,\ldots,n-1\}$ and initial placement of $k$ labelled servers (positions may coincide). Let $L$ be the length of the encoding of $n$, $k$, the entire rational distance matrix in row-major order, and the one-based initial positions in label order. A natural code is a string of as many ones as its `Nat.bits` length, followed by zero then those low-to-high bits; a rational is a negativity bit followed by the framed numerator magnitude and positive denominator.

The machine has a finite control, a read-only input tape and a fixed finite number of work tapes, all two-sided with blank, false and true as symbols. Every tape has a left stack of neighboring cells, scanned cell and right stack; moving left or right pops the head of that stack or a blank if empty, pushing the old cell on the other stack. One transition reads the control, scanned input symbol, the tuple of scanned work symbols, and one bit. It sets the new control, independently moves the input head left/stay/right, overwrites every work head with a blank or bit and then moves each work head independently, optionally appends one output bit, and sets a yield flag. Further transitions are identity while yielded. Interpret the output in emission order as a little-endian natural (empty word zero).

Boot starts at the initial control with the instance word under the input head (head at first symbol), blank work tapes, empty output and no yield, and iterates $c(L+1)^e$ transitions with false bits; it must have yielded. At a request boundary, retain all work tapes and their heads and the control; replace the input tape with the framed one-based request, clear the output and yield, and run $c(L+\lceil\log_2(t+2)\rceil+1)^e$ transitions when $t$ requests have already been processed. For every state reachable from boot with any requests and **all** prior bit strings, every such next run has yielded by its budget and its decoded value is less than $k$. The serving recursion selects the value modulo $k$ to be total, but the preceding requirement precludes using this to mask an invalid label. Move just that zero-based server label to the request and charge its distance.

For every fixed finite sequence, expectation over the independent uniform prescribed bit strings of all requests is at most $C(\log(k+1))^2$ times the offline optimum plus some $B\ge0$ depending on the instance, not on the sequence. The same machine serves all instances. No zero-additive guarantee for distinct initial positions or polynomial bound on $B$ is asserted.

## Depends on

- [The k-server model](the-k-server-problem.md)
- Rational-matrix instance encoding, yielding bit-tape transitions, and all-seed reachability with retained work tapes.

## Proof outline

Define the state-install/yield convention and convert every step and output into an explicit cost model before transferring the competitive proof; establish validity before comparing expected movement. Do not use the totalizing reduction modulo $k$ to excuse an invalid output.

- Uniform finite-rational implementation of the competitive policy and a bit-budget and valid-output induction for every reachable state.

## Sources

- [Comparator statement: `OAI.UniformKServer.uniform_squared_logarithmic_main`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformKServer.lean#L198-L202)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/110.md)
- [Local tape moves, transitions, exact initialization and persistent install](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformKServer.lean#L35-L113)
- [Encoding, budgets, reachability, output and finite uniform expectation](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/UniformKServer.lean#L115-L197)
