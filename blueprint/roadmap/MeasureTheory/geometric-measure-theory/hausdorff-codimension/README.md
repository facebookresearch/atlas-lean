# Hausdorff codimension

Let $S$ be a subset of an extended metric space and let $n$ and $c$ be natural numbers. The set
$S$ has Hausdorff codimension at least $c$ in dimension $n$ when $S$ is empty or its Hausdorff
dimension satisfies $\dim_H S + c \le n$, the inequality being taken in $[0, \infty]$. The empty
case plays the role of the convention $\dim_H \emptyset = -\infty$.

## Idea

In an $n$-dimensional space a point has codimension $n$ and a hypersurface codimension $1$.
Statements about exceptional sets, such as the singular set of a map or of a solution of an
equation, are often phrased by a lower bound on codimension, so that they read the same in every
ambient dimension. The basic facts here are that the bound passes to subsets, that the empty set
has every codimension, that for $c \le n$ it is the dimension bound $\dim_H S \le n - c$, and that
a set whose codimension exceeds the dimension $n$ is empty.

## Statements

- [Lower bound on Hausdorff codimension](has-hausdorff-codim-at-least.md)
- [Characterization of Hausdorff codimension](has-hausdorff-codim-at-least-iff.md): a characterization: for $c \le n$ it is the bound $\dim_H S \le n - c$.
- [A dimension bound gives a codimension bound](has-hausdorff-codim-at-least-of-dim-h-le.md): one direction of the characterization.
- [Subsets inherit a codimension bound](mono.md): a basic fact: the bound passes to subsets.
- [The empty set has every codimension](has-hausdorff-codim-at-least-empty.md): a basic fact about the empty set.
- [Sets of codimension larger than the dimension are empty](eq-empty-of-lt.md): a basic fact: codimension above $n$ forces the empty set.
