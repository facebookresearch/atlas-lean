# Andersen's inclusion constraints

Consider programs whose pointer operations are normalized to the forms $X = \mathtt{alloc}\ P$, where the initial content $P$ of the new cell is $\mathtt{null}$ or an integer constant, $X_1 = \&X_2$, $X_1 = X_2$, $X_1 = {*}X_2$, ${*}X_1 = X_2$ and $X = \mathtt{null}$. An allocation with a pointer-valued initializer is normalized into an allocation followed by a store. The *abstract cells* $\mathrm{Cell}$ are the program variables together with one cell $\mathtt{alloc}\text{-}i$ for each allocation site $i$. Andersen's analysis introduces, for each cell $c$, a constraint variable $[\![c]\!]$ ranging over subsets of $\mathrm{Cell}$, and generates for each operation, regardless of control flow:

- $X = \mathtt{alloc}\ P$ at site $i$: $\mathtt{alloc}\text{-}i \in [\![X]\!]$;
- $X_1 = \&X_2$: $X_2 \in [\![X_1]\!]$;
- $X_1 = X_2$: $[\![X_2]\!] \subseteq [\![X_1]\!]$;
- $X_1 = {*}X_2$: $c \in [\![X_2]\!] \implies [\![c]\!] \subseteq [\![X_1]\!]$ for each $c \in \mathrm{Cell}$;
- ${*}X_1 = X_2$: $c \in [\![X_1]\!] \implies [\![X_2]\!] \subseteq [\![c]\!]$ for each $c \in \mathrm{Cell}$;
- $X = \mathtt{null}$: no constraint.

The constraints have a least solution, and the *points-to sets* are $\mathrm{pt}(p) = [\![p]\!]$ in it. Variables $X$ with no occurrence of $\&X$ in the program may be omitted from the conditional constraints. The analysis is flow-insensitive, but the direction of the inclusions models the direction of dataflow.

## Depends on

- [Closure analysis (0-CFA) and the cubic algorithm](../closure-analysis-0-cfa-and-the-cubic-algorithm.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.1 (the allocation-site abstraction and abstract cells) and Section 11.2 (the six normalized pointer operations, with $P$ in $\mathtt{alloc}\ P$ restricted to $\mathtt{null}$ or an integer constant, the constraint for each, the definition $\mathrm{pt}(p) = [\![p]\!]$ in the least solution, and the worked example).
