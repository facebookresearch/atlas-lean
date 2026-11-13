# Influence sets of wires

Given a list $ps$ of comparators on wires indexed by $\mathbb{N}$
and an assignment $S$ of a finite set of natural numbers to each wire, the influence sets after
$ps$ are computed by processing the comparators in order: a comparator $(i, j)$ replaces the
current sets of both wires $i$ and $j$ by their union, and leaves the sets of all other wires
unchanged. Starting from $S(x) = \{x\}$, the set of a wire tracks the inputs it can depend on.

Evaluating this definition directly re-reads both wires' earlier sets at every comparator, a cost
exponential in the depth, so it serves as a proof device only.
