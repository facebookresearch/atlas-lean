# Deterministic polynomial-bit construction of strong thin trees

There are a real $C>0$, integers $a>0,d\ge0$, and one deterministic finite-control bit-stack machine with the following property. Take a loopless multigraph on $n\ge1$ labelled vertices with every nonempty proper cut containing at least $k\ge1$ edges. Input has either tag zero followed by $n,m,k$ and all $m$ ordered endpoint pairs in edge-index order (endpoints need not be increasingly ordered within an explicit record), or tag one followed by $n,p,k$ and the $p$ distinct increasing endpoint pairs each followed by its natural multiplicity. In the latter case each edge is a pair of record index and copy index less than that record’s multiplicity. Every natural, including output indices, is encoded by writing $0b$ per bit $b$ in its low-to-high binary numeral and ending with $1$ (the payload for zero is empty).

The fixed machine has finitely many bit stacks, finitely many states, and designated input and output stacks. Its initial state is designated, with the input word on the input stack and all other stacks empty. Encode a stack head as $0$ if empty, $1$ for false, and $2$ for true. Read the tuple of top tags as a base-three integer with stack zero least significant. At state index $q$ the table index is $3^{s}q$ plus that integer for $s$ stacks. Each entry consists of an optional next state and one action per stack: stay, pop, or push a specified bit. These actions are applied simultaneously; pop on an empty stack leaves it empty. A missing row halts with all stacks unchanged, and an absent state is absorbing. This is one charged step, not a `FinTM2` statement-block step. No requirement resets work stacks after halt.

After $a(L+1)^d$ such steps, where $L$ is the exact input length, the state is absent and the designated output stack contains the framed list of selected edge indices (record and copy index pairs in compressed mode) with no repeated edge. These edges span and form a tree, and each nonempty proper cut meets at most $C/k$ times its original edge count in selected edges. At $n=1$ the output bit list is empty. Parallel edges remain distinct in the cut counts.

## Depends on

- Edge-labelled multigraph cut connectivity and thin-tree inequality, and deterministic bit-stack transition and framing semantics.

## Proof outline

Treat the explicit and compressed encodings separately and show the binary path need not materialize the full edge expansion. Prove correctness for all valid inputs in one machine, including the singleton empty-output rule.

- Deterministic thin-tree selection and polynomial work with binary multiplicities, with a decoding proof for edge-copy identifiers.

## Sources

- [Comparator statement: `OAI.AlgorithmicThinTrees.algorithmic_strong_thin_trees`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AlgorithmicThinTrees.lean#L191-L193)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/174.md)
- [Encoding, table lookup, stack actions and execution](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AlgorithmicThinTrees.lean#L35-L95)
- [Input, selected edges and exact output predicate](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/AlgorithmicThinTrees.lean#L101-L189)
