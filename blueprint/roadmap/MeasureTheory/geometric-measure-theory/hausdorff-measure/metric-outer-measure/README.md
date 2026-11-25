# Metric outer measures

Let $X$ be an extended metric space, in which distances may be infinite, such as a metric space. An outer measure $\mu$
on $X$ is a metric outer measure if $\mu(A \cup B) = \mu(A) + \mu(B)$ whenever $A$ and $B$ are metrically separated:
some $r > 0$ satisfies $r \le d(a, b)$ for all $a \in A$ and $b \in B$. This is the general form of the definition for a
metric space $(X, \rho)$, where separation says that the distance $\rho(A, B) = \inf\{\rho(a, b) : a \in A,\ b \in B\}$
is positive.

## Idea

Additivity on sets at positive distance is what makes Borel sets measurable in Carathéodory's sense, so a metric outer
measure restricts to a measure on the Borel σ-algebra. Lebesgue outer measure on $\mathbb{R}^n$ and the Hausdorff outer
measures are metric outer measures: once the sets of a cover have diameter less than the distance between $A$ and $B$,
the cover splits into a cover of $A$ and a cover of $B$, and for Lebesgue outer measure covers by small boxes suffice,
since a box splits into small boxes of the same total volume.

## Statements

- [Metric outer measure](is-metric.md)
