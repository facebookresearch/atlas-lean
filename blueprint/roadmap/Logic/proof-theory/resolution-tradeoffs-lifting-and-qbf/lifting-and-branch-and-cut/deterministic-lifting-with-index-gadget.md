# Deterministic query-to-communication lifting with the index gadget

Composing any Boolean function on $N$ bits with the index gadget on $m = N^{20}$ points multiplies its deterministic decision-tree complexity by $\Theta(\log N)$ to give the deterministic communication complexity of the composition.

**Theorem (Raz-McKenzie simulation theorem).** Let $g : [m] \times \{0,1\}^m \to \{0,1\}$, $g(x, y) = y_x$, be the index gadget with $m := N^{20}$, so Alice's part of each gadget has $\log m = \Theta(\log N)$ bits. For every $f : \{0,1\}^N \to \{0,1\}$,

$$
P^{cc}(f \circ g^N) = P^{dt}(f) \cdot \Theta(\log N),
$$

where $P^{cc}$ is deterministic communication complexity of the two-party function $(x, y) \mapsto f(g(x_1, y_1), \dots, g(x_N, y_N))$ with $x \in [m]^N$ given to Alice and $y \in (\{0,1\}^m)^N$ to Bob, and $P^{dt}$ is deterministic decision-tree depth. The lower bound holds equally when $f$ is a partial function, a search problem or has non-Boolean range.

## Expansion

The upper bound is the trivial simulation: whenever the decision tree queries $z_i$, Alice and Bob spend $\lceil \log m \rceil + 1$ bits to compute $g(x_i, y_i)$. For the lower bound, fix a protocol of cost $k = o(N \log m)$ and simulate it by a decision tree: maintain a rectangle $A \times B$ inside the current protocol node on which the outputs of $g^N$ realize exactly the values of the unqueried coordinates consistent with the queries made so far. When no unqueried coordinate is too predictable, let the protocol send a bit and clean up with the Thickness Lemma; when some coordinate $i$ becomes predictable, query $z_i$ and restore the invariants with the Projection Lemma. A potential argument shows each communication step raises the potential by $O(1)$ while each query lowers it by $\Omega(\log m)$, so the decision tree makes $O(k / \log m)$ queries. In proof complexity, lifting theorems of this kind turn decision-tree (resolution-depth type) lower bounds for search problems into communication lower bounds that bound tree-like cutting planes and related systems.

## Depends on

- [Composed functions, gadgets and lifting theorems](../../../../TheoryOfComputation/communication-complexity/randomized-and-dag-like-lifting/composed-function-lifting.md)
- [Deterministic communication complexity](../../../../TheoryOfComputation/communication-complexity/deterministic-communication-protocols/comm-complexity.md)
- [Decision-tree depth and degree of a Boolean function](../../../../TheoryOfComputation/communication-complexity/query-and-communication-measures/decision-tree-depth-and-degree-of-a-boolean.md)

## Proof depends on

None.

## Sources

- M. Göös, T. Pitassi, T. Watson, "Deterministic communication vs. partition number", *SIAM Journal on Computing* 47(6), 2018 (conference version FOCS 2015), doi:10.1137/16M1059369; numbering from the ECCC TR15-050 edition read (Theorem 3 in Section 1; Section 3 with the gadget choice $m := N^{20}$, Lemmas 6 and 7).
