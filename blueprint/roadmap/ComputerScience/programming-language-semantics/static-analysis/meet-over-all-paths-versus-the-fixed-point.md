# The meet-over-all-paths solution versus the fixed-point solution

Let $L$ be a lattice of finite height, and consider a forward dataflow analysis on a finite control-flow graph with an entry node $s$ that has no predecessors. Each node $n$ has a monotone transfer function $f_n : L \to L$, and $\iota \in L$ is the value at the entry. Write in the join ($\sqcup$) convention of [monotone frameworks](monotone-frameworks-and-the-worklist-algorithm.md), where larger means less precise.

- The **fixed-point solution** $\mathrm{MFP}$ is the least solution of $x_s = f_s(\iota)$ and $x_n = f_n\bigl(\bigsqcup_{p \to n} x_p\bigr)$ for $n \ne s$, computed by iteration.
- The **meet-over-all-paths solution** $\mathrm{MOP}(n)$ is the join, over all paths $s = n_0 \to n_1 \to \dots \to n_k = n$, of $f_{n_k}(\cdots f_{n_1}(f_{n_0}(\iota)) \cdots)$. It propagates information separately along each path and combines only at the end.

Suppose every node is reachable from $s$.

1. $\mathrm{MOP}(n) \sqsubseteq \mathrm{MFP}(n)$ for every node $n$. The fixed-point solution is safe with respect to the path-based ideal but possibly less precise.
2. If every $f_n$ is *distributive*, $f_n(x \sqcup y) = f_n(x) \sqcup f_n(y)$, then $\mathrm{MOP}(n) = \mathrm{MFP}(n)$ for every node $n$.

**Proof.** For part 1, show by induction on the length of a path ending in $n$ that its value lies below $\mathrm{MFP}(n)$. Use that $\mathrm{MFP}$ satisfies the equations and that every $f_n$ is monotone. For part 2, $\mathrm{MOP}$ itself satisfies the equations. By finite height, each join over the infinitely many paths into a predecessor equals a finite join. Distributivity moves the joins at merge points through the transfer functions, and reachability makes every such join nonempty. Since $\mathrm{MFP}$ is the least solution, $\mathrm{MFP} \sqsubseteq \mathrm{MOP}$, and with part 1 the two are equal.

In the dual convention of a meet semilattice, the dataflow solution is the greatest fixed point and is at most as informative as the meet over paths, with equality for distributive transfer functions. Live-variables analysis, with transfer functions $\ell \mapsto \mathit{use}[n] \cup (\ell \setminus \mathit{def}[n])$, is distributive. Constant propagation is not.

## Depends on

- [Monotone frameworks and the work-list algorithm](monotone-frameworks-and-the-worklist-algorithm.md)

## Sources

- A. C. Myers, *The Meet-Over-Paths Criterion*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/mop/index.html>: the dataflow and meet-over-paths solutions, equality under distributivity, the live-variables example and the non-distributive constant-propagation analysis.
- J. B. Kam and J. D. Ullman, "Monotone data flow analysis frameworks", *Acta Informatica* 7(3):305–317, 1977.
