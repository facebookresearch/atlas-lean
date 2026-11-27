# Separating examples for multiclass learning dimensions

1. (Hexagon class.) The class $H = \{f : \{0,1\} \to \{0,1,2\} : f(0) \ne f(1)\}$ of six labelings of two points has Natarajan dimension $1$, DS dimension $2$ (its six members form a $2$-dimensional pseudo-cube, a $6$-cycle) and graph dimension $2$.
2. (Revealing-subset class.) For a set $X$, let $\beta$ be the set of values $\{\bot\} \cup \{\text{finite subsets of } X\}$ and, for each finite $B \subseteq X$, let $r_B(x) = \bot$ for $x \in B$ and $r_B(x) = B$ otherwise. The class $\{r_B\}$ G-shatters every finite subset of $X$, so it has infinite graph dimension when $X$ is infinite, while on every nonempty $X$ its DS dimension and Natarajan dimension equal $1$.

Hence the inequalities $\mathrm{Ndim} \le \mathrm{DSdim} \le \mathrm{Gdim}$ can be strict, and over infinite label sets finite DS dimension does not imply finite graph dimension.

## Proof sketch

No $2 \times 2$ product of label sets fits inside the off-diagonal of $\{0,1,2\}^2$, so the hexagon class N-shatters no two points, while each of its labelings has a neighbour in each coordinate. For the revealing class, the constant reference $\bot$ witnesses G-shattering of any finite set, but any non-$\bot$ value identifies $B$, which prevents a two-dimensional pseudo-cube.

## Depends on

- [Natarajan, DS and graph dimensions compared](natarajan-ds-and-graph-dimensions.md)
- [Graph dimension of a multiclass concept class](graph-dimension.md)
- [DS dimension characterizes multiclass PAC learnability](../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- A. Daniely and S. Shalev-Shwartz, "Optimal Learners for Multiclass Problems", Proceedings of the 27th Conference on Learning Theory (COLT), 2014.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran and A. Yehudayoff, "A Characterization of Multiclass Learnability", IEEE 63rd Annual Symposium on Foundations of Computer Science (FOCS), 2022.
- S. Ben-David, N. Cesa-Bianchi, D. Haussler and P. M. Long, "Characterizations of Learnability for Classes of {0, ..., n}-Valued Functions", Journal of Computer and System Sciences, 1995.
