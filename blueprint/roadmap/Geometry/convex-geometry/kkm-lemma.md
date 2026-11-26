# Knaster–Kuratowski–Mazurkiewicz lemma

Let $F_0, \dots, F_n$ be closed subsets of the standard simplex
$\Delta^n = \{x \in \mathbb{R}^{n+1} : x_i \ge 0,\ \sum_i x_i = 1\}$ such that every point $x$ lies in some $F_i$
with $x_i > 0$. Then the sets $F_i$ have a common point.

The covering hypothesis is the KKM condition in pointwise form: a point $x$ lies in the face spanned by the vertices
of its support, so "every face $\operatorname{conv}\{e_i : i \in I\}$ is covered by $\bigcup_{i \in I} F_i$" is
equivalent to it. The proof applies Sperner's lemma to the labelling $x \mapsto i$ on the vertices of the $k$-th
iterated barycentric subdivision, obtains a fully labelled cell at every level, and passes to the limit using
compactness, the mesh bound $(n/(n+1))^k$ and closedness of the $F_i$.

## Informally uses

- [Sperner's lemma](../../Combinatorics/polytopes-simplicial-complexes/sperner-s-lemma/README.md): the $n$-dimensional lemma on iterated barycentric subdivisions.

## Background

- [Brouwer's fixed-point theorem for the standard simplex](../../Topology/algebraic-topology/brouwer-fixed-point-theorem/exists-fixed-point.md): the consequence announced in the title of the KKM paper, derived from this lemma.

## Sources

- B. Knaster, C. Kuratowski, S. Mazurkiewicz, "Ein Beweis des Fixpunktsatzes für n-dimensionale Simplexe", Fundamenta Mathematicae 14 (1929), 132–137.
