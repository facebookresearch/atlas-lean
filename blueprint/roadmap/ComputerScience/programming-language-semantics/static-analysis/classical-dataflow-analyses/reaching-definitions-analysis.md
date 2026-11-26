# Reaching definitions analysis

Let a program be given as a control-flow graph whose nodes are statements, with an entry node that has no predecessors and is not an assignment, and call each assignment node $X = E$ a *definition* of $X$. A definition $d$ of $X$ *reaches* a program point if some path in the graph from $d$ to that point contains no other definition of $X$.

*Reaching definitions analysis* approximates, for every node $v$, the set of definitions that may reach the point after $v$. It uses the powerset lattice $(\mathcal{P}(\mathrm{Defs}), \subseteq)$ of the assignment nodes of the program and a constraint variable $[\![v]\!]$ for each node, with

$$\mathrm{JOIN}(v) = \bigcup_{w \in \mathrm{pred}(v)} [\![w]\!].$$

The constraints are

- $[\![v]\!] = (\mathrm{JOIN}(v) \downarrow X) \cup \{v\}$ for an assignment $v$ of the form $X = E$, where $S \downarrow X$ removes from $S$ every definition of $X$;
- $[\![v]\!] = \mathrm{JOIN}(v)$ for every other node, so that $[\![\mathit{entry}]\!] = \emptyset$.

The right-hand sides are monotone, so the constraints have a least solution, which is the result of the analysis. It is a forward *may* analysis: the computed sets may be too large but contain every definition that reaches the point along some path. Equivalently, with $\mathit{gen}[v] = \{v\}$ and $\mathit{kill}[v]$ the set of all definitions of $X$ for an assignment $v$ to $X$, and both empty otherwise, the transfer function of $v$ is $\ell \mapsto \mathit{gen}[v] \cup (\ell \setminus \mathit{kill}[v])$.

## Depends on

- [Monotone frameworks and the work-list algorithm](../monotone-frameworks-and-the-worklist-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 5.7 (the lattice of assignments, $\mathrm{JOIN}$ over predecessors and the constraint for assignments) and Section 5.8 (forward and may analyses).
- A. C. Myers, *Reaching definitions and SSA*, lecture notes for CS 4120, Cornell University, 2022, <https://courses.cs.cornell.edu/courses/cs4120/2022sp/notes/reachdef/index.html>: the definition of reaching, the dataflow equations $\mathit{in}[n] = \bigcup_{n' \prec n} \mathit{out}[n']$ and $\mathit{out}[n] = \mathit{gen}[n] \cup (\mathit{in}[n] - \mathit{kill}[n])$, and the gen and kill table.
