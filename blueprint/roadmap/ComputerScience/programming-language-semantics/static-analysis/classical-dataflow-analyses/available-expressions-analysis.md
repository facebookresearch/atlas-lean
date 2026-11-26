# Available expressions analysis

Let a program be given as a control-flow graph whose nodes are statements, with an entry node that has no predecessors and performs no computation. A nontrivial expression (one built with an operator) is *available* at a program point if, on every path from the entry to that point, it is computed and none of its variables is assigned afterwards on that path.

*Available expressions analysis* approximates, for every node $v$, the set of expressions available at the point after $v$. Let $\mathrm{Exps}$ be the finite set of nontrivial expressions occurring in the program, and use the lattice $(\mathcal{P}(\mathrm{Exps}), \supseteq)$, ordered by reverse inclusion, whose least element is $\mathrm{Exps}$ and whose top element is $\emptyset$. With a constraint variable $[\![v]\!]$ for each node,

$$\mathrm{JOIN}(v) = \bigcap_{w \in \mathrm{pred}(v)} [\![w]\!].$$

Write $\mathrm{exps}(E)$ for the nontrivial subexpressions of $E$, including $E$ itself when it is nontrivial, and $S \downarrow X$ for $S$ without the expressions that contain the variable $X$. The constraints are

- $[\![\mathit{entry}]\!] = \emptyset$;
- $[\![v]\!] = (\mathrm{JOIN}(v) \cup \mathrm{exps}(E)) \downarrow X$ for an assignment $X = E$;
- $[\![v]\!] = \mathrm{JOIN}(v) \cup \mathrm{exps}(E)$ for a branch condition $E$ and for an output statement $E$;
- $[\![v]\!] = \mathrm{JOIN}(v)$ for every other node.

The right-hand sides are monotone, so the constraints have a least solution in this lattice, that is, the largest family of sets satisfying them, which is the result of the analysis. It is a forward *must* analysis: the computed sets may be too small but contain only expressions that are available whichever path reached the point. The expressions available before a node $v$ other than the entry are $\mathrm{JOIN}(v)$; before the entry none is available, although the intersection over its empty set of predecessors would be all of $\mathrm{Exps}$. Each transfer function has the gen/kill form $\ell \mapsto \mathit{gen}[v] \cup (\ell \setminus \mathit{kill}[v])$: for an assignment $X = E$, $\mathit{gen}[v] = \mathrm{exps}(E) \downarrow X$ and $\mathit{kill}[v]$ is the set of expressions containing $X$.

## Depends on

- [Monotone frameworks and the work-list algorithm](../monotone-frameworks-and-the-worklist-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 5.5 (the reverse-inclusion lattice, $\mathrm{JOIN}$ by intersection over predecessors, the functions $\downarrow X$ and $\mathrm{exps}$, and the constraints for entry, assignment, condition and output nodes) and Section 5.8 (forward and must analyses).
- A. C. Myers, *Redundancy elimination*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/cse/index.html>: available expressions analysis as the basis of common subexpression elimination.
