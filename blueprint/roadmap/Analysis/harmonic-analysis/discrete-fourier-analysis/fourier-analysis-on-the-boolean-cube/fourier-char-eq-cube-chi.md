# Subset characters agree with cube characters

Let $E$ be a finite set with $m$ elements,
listed in a fixed order as $e_0, \dots, e_{m-1}$, and encode a subset $T \subseteq E$ as the point
$x_T$ of the Boolean cube of dimension $m$ whose $j$-th coordinate is false exactly when
$e_j \in T$. For all subsets $S, T \subseteq E$,

$$(-1)^{|S \cap T|} = \chi_{S'}(x_T),$$

where the left side is the Fourier character of $S$ at $T$, $S' = \{j : e_j \in S\}$ is $S$
reindexed as a set of coordinates, and $\chi_{S'}$ is the Fourier character on the cube.
