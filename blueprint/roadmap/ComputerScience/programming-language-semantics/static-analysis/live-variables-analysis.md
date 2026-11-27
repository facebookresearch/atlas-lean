# Live-variables analysis

A variable is *live* at a program point if there is an execution in which its value is read later without being written in between; this property is undecidable. *Live-variables analysis* approximates it on a control-flow graph with the parameterized powerset lattice $(\mathcal{P}(\mathrm{Vars}), \subseteq)$ of the program's variables, assigning to every node $v$ a constraint variable $[\![v]\!]$ for the set of variables live before $v$. With $\mathrm{JOIN}(v) = \bigcup_{w \in \mathrm{succ}(v)} [\![w]\!]$, the constraints are

- $[\![v]\!] = (\mathrm{JOIN}(v) \setminus \{X\}) \cup \mathrm{vars}(E)$ for an assignment $X = E$;
- $[\![v]\!] = \mathrm{JOIN}(v) \cup \mathrm{vars}(E)$ for a branch condition $E$ (of an `if` or a `while`) and for `output` $E$;
- $[\![v]\!] = \mathrm{JOIN}(v) \setminus \{X_1, \dots, X_n\}$ for a declaration `var` $X_1, \dots, X_n$;
- $[\![\mathit{exit}]\!] = \emptyset$, and $[\![v]\!] = \mathrm{JOIN}(v)$ for every other node,

where $\mathrm{vars}(E)$ is the set of variables occurring in $E$. These right-hand sides are monotone, so the constraints have a least solution, which is the result of the analysis. The analysis is a backward analysis designed to be conservative in the direction in which the answer "not live" can be trusted. For a program with $n$ control-flow-graph nodes and $b$ variables, the naive fixed-point algorithm computes it in time $O(b^2 n^2)$.

## Depends on

- [Monotone frameworks and the worklist algorithm](monotone-frameworks-and-the-worklist-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, 2022, <https://cs.au.dk/~amoeller/spa/>, Section 5.4
