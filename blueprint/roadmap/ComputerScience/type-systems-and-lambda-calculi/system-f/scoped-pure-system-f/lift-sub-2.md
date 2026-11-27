# Lifting a term substitution under a term lambda

For a term substitution $\sigma$ assigning to each $i < m$ a [term](tm.md) $\sigma(i) \in \mathrm{Tm}_{n,k}$, its lifting under a term abstraction assigns $x_0$ to $0$ and, to $i + 1$, the term $\sigma(i)$ with term variables [renamed](rename-2.md) by $j \mapsto j + 1$; it is a substitution from $m + 1$ to $k + 1$ term variables.
