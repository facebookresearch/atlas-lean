# Andersen's analysis is at least as precise as Steensgaard's

For every program with normalized pointer operations, let $\mathrm{pt}_A$ be the points-to sets of [Andersen's analysis](andersen-s-inclusion-constraints.md) and $\mathrm{pt}_S$ those of [Steensgaard's analysis](steensgaard-s-unification-constraints.md). Then $\mathrm{pt}_A(p) \subseteq \mathrm{pt}_S(p)$ for every variable $p$.

**Proof idea.** The sets $S(c) = \mathrm{pt}_S(c)$, for each cell $c$, satisfy all of Andersen's constraints. An allocation or address-of operation puts its cell into $S$ of its target by the equation $[\![X]\!] = {\uparrow}[\![\cdot]\!]$. An assignment equates the two term variables, so their sets are equal. For a load $X_1 = {*}X_2$, if $c \in S(X_2)$ then $[\![X_2]\!] = {\uparrow}[\![c]\!]$ and $[\![X_2]\!] = {\uparrow}\alpha$ with $[\![X_1]\!] = \alpha$, so by injectivity $[\![c]\!] = [\![X_1]\!]$ and $S(c) = S(X_1)$; stores are symmetric. Andersen's result is the least solution, hence below $S$. On the example program of the notes the inclusion is strict.

## Depends on

- [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md)
- [Steensgaard's unification constraints](steensgaard-s-unification-constraints.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.4 (the example on which Steensgaard's result is less precise than Andersen's) and Exercise 11.13 ("Prove that Andersen's analysis is always at least as precise as Steensgaard's analysis"). The proof idea above is written out here.
