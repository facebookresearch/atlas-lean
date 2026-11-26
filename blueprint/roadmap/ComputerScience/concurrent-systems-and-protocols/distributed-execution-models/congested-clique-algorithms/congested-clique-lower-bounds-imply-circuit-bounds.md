# Congested clique lower bounds imply circuit lower bounds

In the congested clique with each processor holding $n$ input bits, every Boolean function computable by a family of bounded-depth circuits of polynomial size with unbounded fan-in AND, OR, NOT and MOD gates (and suitably bounded wiring) can be computed in $O(1)$ rounds. Consequently, any super-constant lower bound on the number of rounds needed for an explicit function in the congested clique would yield a new lower bound against such constant-depth circuit classes, beyond current techniques. In contrast, a counting argument shows that most Boolean functions of the $n^2$ input bits require $\Omega(n / \log n)$ rounds.

## Proof sketch

Simulate a circuit layer by layer: assign gates to processors so that each processor computes $O(n)$ gates per layer, and route the outputs of each layer to the gates of the next using Lenzen routing, which costs $O(1)$ rounds per layer when the wiring is balanced; unbounded fan-in gates are evaluated by aggregating partial results through intermediate processors. For the counting bound, a $t$-round protocol is determined by the processors' local functions on at most $O(t n \log n)$ received bits plus their inputs, which bounds the number of computable functions below $2^{2^{n^2}}$ when $t = o(n / \log n)$.

## Depends on

- [The congested clique model](the-congested-clique-model.md)

## Proof depends on

- [Lenzen's deterministic constant-round routing and sorting in the congested clique](congested-clique-constant-round-routing.md)

## Sources

- A. Drucker, F. Kuhn, R. Oshman, "On the Power of the Congested Clique Model", PODC 2014.
