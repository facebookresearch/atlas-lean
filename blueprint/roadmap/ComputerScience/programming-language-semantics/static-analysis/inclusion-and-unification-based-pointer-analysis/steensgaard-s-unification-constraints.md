# Steensgaard's unification constraints

For programs with the normalized pointer operations and abstract cells of [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md), Steensgaard's analysis uses a term variable $[\![c]\!]$ for each abstract cell $c$ and a unary term constructor $\uparrow$, where $\uparrow t$ stands for a pointer to $t$. It generates the equations

- $X = \mathtt{alloc}\ P$ at site $i$: $[\![X]\!] = {\uparrow}[\![\mathtt{alloc}\text{-}i]\!]$;
- $X_1 = \&X_2$: $[\![X_1]\!] = {\uparrow}[\![X_2]\!]$;
- $X_1 = X_2$: $[\![X_1]\!] = [\![X_2]\!]$;
- $X_1 = {*}X_2$: $[\![X_2]\!] = {\uparrow}\alpha$ and $[\![X_1]\!] = \alpha$ for a fresh term variable $\alpha$;
- ${*}X_1 = X_2$: $[\![X_1]\!] = {\uparrow}\alpha$ and $[\![X_2]\!] = \alpha$ for a fresh term variable $\alpha$;

at most two per operation, and solves them by unification under the injectivity axiom ${\uparrow}\alpha_1 = {\uparrow}\alpha_2 \implies \alpha_1 = \alpha_2$. Unification never fails, since $\uparrow$ is the only constructor. The points-to sets are

$$\mathrm{pt}(p) = \{t \in \mathrm{Cell} \mid [\![p]\!] = {\uparrow}[\![t]\!]\}$$

in the most general unifier. Assignments are thus treated as bidirectional: after $X_1 = X_2$ the two variables have the same points-to set.

## Depends on

- [Andersen's inclusion constraints](andersen-s-inclusion-constraints.md)

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>: Section 11.4 (the term variables and the constructor $\uparrow$, the constraint for each operation, the injectivity axiom, the definition of $\mathrm{pt}$, and the remark that unification never fails; Steensgaard's original conditional unification for assignments is not used).
