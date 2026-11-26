# Directed phi-expander hierarchies of a directed graph

Let $G=(V,E)$ be a directed graph and $0<\phi\le 1$. A partition $\mathcal{H}=(D,X_1,\dots,X_\eta)$ of $E$ is a *$\phi$-expander hierarchy of height $\eta$* if

1. the edge set $D$ (the *DAG edges*) is acyclic, and
2. for every $i\in\{1,\dots,\eta\}$, the set $X_i$ is $\phi$-expanding in $G\setminus X_{>i}$, where $X_{>i}=X_{i+1}\cup\dots\cup X_\eta$; that is, every strongly connected component of $G\setminus X_{>i}$ is a $\phi$-expander with respect to the edges of $X_i$ it contains.

In particular $X_\eta$ is $\phi$-expanding in $G$ itself. The hierarchy generalizes the undirected expander hierarchies of Pătraşcu-Thorup type by allowing acyclic edges $D$ between components; a one-level hierarchy $(D,X_1)$ is a directed acyclic arrangement of $\phi$-expanders.

## Depends on

- [Directed phi-expanders, phi-sparse directed cuts, and phi-expanding terminal edge sets](directed-phi-expanders.md)
- [Acyclic condensation](../../../ComputerScience/graph-algorithms/traversal-and-connectivity/strongly-connected-components/condensation-acyclic.md)

## Sources

- Aaron Bernstein, Joakim Blikstad, Thatchaphol Saranurak, Ta-Wei Tu, "Maximum Flow by Augmenting Paths in n^(2+o(1)) Time", FOCS (2024), arXiv:2406.03648.
