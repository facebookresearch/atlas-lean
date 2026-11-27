# Gen/kill transfer functions are distributive

Let $U$ be a finite set and, for sets $\mathit{gen}, \mathit{kill} \subseteq U$, let $f(\ell) = \mathit{gen} \cup (\ell \setminus \mathit{kill})$ on $\mathcal{P}(U)$.

1. **Distributivity.** For all $\ell_1, \ell_2 \subseteq U$,

    $$f(\ell_1 \cup \ell_2) = f(\ell_1) \cup f(\ell_2) \quad\text{and}\quad f(\ell_1 \cap \ell_2) = f(\ell_1) \cap f(\ell_2).$$

    So $f$ is distributive in the lattice $(\mathcal{P}(U), \subseteq)$, whose join is $\cup$, and in $(\mathcal{P}(U), \supseteq)$, whose join is $\cap$.
2. **Meet over all paths.** [Live-variables analysis](../live-variables-analysis.md), [reaching definitions analysis](reaching-definitions-analysis.md), [available expressions analysis](available-expressions-analysis.md) and [very busy expressions analysis](very-busy-expressions-analysis.md) have transfer functions of this form. Hence, on a finite control-flow graph whose entry node has no predecessors and whose exit node has no successors, in which every node is reachable from the entry node and the exit node is reachable from every node, the least solution of each of these analyses equals its meet-over-all-paths solution. The paths are taken in the direction of the analysis: from the entry for the forward analyses and from the exit, along reversed edges, for the backward ones.

**Proof.** Part 1: set difference distributes over union and intersection, $(\ell_1 \cup \ell_2) \setminus K = (\ell_1 \setminus K) \cup (\ell_2 \setminus K)$ and likewise for $\cap$. Then

$$\mathit{gen} \cup \bigl((\ell_1 \setminus \mathit{kill}) \cup (\ell_2 \setminus \mathit{kill})\bigr) = f(\ell_1) \cup f(\ell_2),$$

and, because union distributes over intersection,

$$\mathit{gen} \cup \bigl((\ell_1 \setminus \mathit{kill}) \cap (\ell_2 \setminus \mathit{kill})\bigr) = f(\ell_1) \cap f(\ell_2).$$

Part 2: the transfer functions are the gen/kill forms stated on the pages of the four analyses, the lattices are finite, and the theorem comparing the [meet-over-all-paths and fixed-point solutions](../meet-over-all-paths-versus-the-fixed-point.md) gives equality for distributive transfer functions. A backward analysis is a forward analysis of the reversed graph, whose entry is the exit node.

## Depends on

- [Live-variables analysis](../live-variables-analysis.md)
- [Reaching definitions analysis](reaching-definitions-analysis.md)
- [Available expressions analysis](available-expressions-analysis.md)
- [Very busy expressions analysis](very-busy-expressions-analysis.md)
- [The meet-over-all-paths solution versus the fixed-point solution](../meet-over-all-paths-versus-the-fixed-point.md)

## Sources

- A. C. Myers, *The Meet-Over-Paths Criterion*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/mop/index.html>: section "Distributivity" (equality of the dataflow and meet-over-paths solutions for distributive transfer functions) and section "Example" (the computation showing that $F_n(\ell) = \mathit{use}[n] \cup (\ell - \mathit{def}[n])$ is distributive, and the remark that analyses with transfer functions of the same form are distributive too).
- A. C. Myers, *Reaching definitions and SSA*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/reachdef/index.html>: the remark that the transfer functions of reaching definitions have the standard gen/kill form, are monotonic and distributive, and so reach the meet-over-paths solution.
- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 5.8 (the classification of the four powerset analyses as forward or backward, may or must) and Exercise 5.34 (which of these analyses are distributive).
