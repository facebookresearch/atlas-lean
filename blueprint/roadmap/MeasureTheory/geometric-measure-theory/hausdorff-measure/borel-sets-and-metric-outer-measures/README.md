# Borel sets are measurable for a metric outer measure

Let $\mu$ be a metric outer measure on an extended metric space $X$, in which distances may be infinite, such as a
metric space. Then every Borel subset $B$ of $X$ is Carathéodory measurable for $\mu$:
$\mu(E) = \mu(E \cap B) + \mu(E \setminus B)$ for every $E \subseteq X$. Hence, by Carathéodory's theorem, the
restriction of $\mu$ to the Borel sets is a measure. This is the general form of the theorem for metric spaces, which
are the extended metric spaces whose distances are finite.

## Idea

The Carathéodory measurable sets form a σ-algebra, so it suffices to treat a closed set $F$. For $E \subseteq X$ with
$\mu(E) < \infty$, the case $\mu(E) = \infty$ being trivial, the sets $E_n = \{x \in E : d(x, F) \ge 1/n\}$ are at
positive distance from $E \cap F$, so $\mu(E \cap F) + \mu(E_n) \le \mu(E)$. The points of $E \setminus F$ outside $E_n$
lie in the sets $R_k = \{x \in E : 1/(k+1) \le d(x, F) < 1/k\}$, $k \ge n$, the rings intersected with $E$. Two of these
sets $R_k$ and $R_j$ with $|k - j| \ge 2$ are at positive distance, so finite sums of the measures of
$R_n, R_{n+2}, \ldots$ are at most $\mu(E)$, and likewise for $R_{n+1}, R_{n+3}, \ldots$; hence $\sum_k \mu(R_k)$ is
finite, and $\mu(E_n) \to \mu(E \setminus F)$. This makes Lebesgue measure and the Hausdorff measures measures on the
Borel sets.

## Statements

- [Borel sets are Carathéodory measurable for a metric outer measure](borel-le-caratheodory.md)

## Background

- [Metric outer measures](../metric-outer-measure/README.md): the hypothesis
- [σ-algebras](../../../measurable-spaces/measurable-spaces-and-measurable-functions/sigma-algebras/README.md): the Borel σ-algebra
- [Carathéodory measurable sets](../../../measures/carath-odory-measurability-for-outer-measures/carath-odory-measurable-sets/README.md): the notion of measurability in the statement
