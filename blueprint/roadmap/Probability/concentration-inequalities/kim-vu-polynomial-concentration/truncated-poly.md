# Partial derivative of a positive polynomial

Let $H$ be a hypergraph on $\{1, \dots, n\}$ with edge set $E$ and positive weights $w$, and let $Y_H = \sum_{e \in E} w(e) \prod_{i \in e} t_i$. For a set $A$ of variables, the truncated hypergraph $H_A$ has edges $e \setminus A$ for the edges $e \supseteq A$, with weight $w(e)$, so

$$Y_{H_A} = \sum_{e \in E,\ A \subseteq e} w(e) \prod_{i \in e \setminus A} t_i,$$

the partial derivative of $Y_H$ with respect to the variables in $A$. For $A = \emptyset$ it is $Y_H$ itself. Here $t_i$ is $1$ or $0$ according as the $i$-th coordinate of $\omega$ is true or false.

## Sources

- J. H. Kim and V. H. Vu, "Concentration of multivariate polynomials and its applications", *Combinatorica* 20 (2000), 417–434, Section 1.2 (truncated subhypergraphs).
