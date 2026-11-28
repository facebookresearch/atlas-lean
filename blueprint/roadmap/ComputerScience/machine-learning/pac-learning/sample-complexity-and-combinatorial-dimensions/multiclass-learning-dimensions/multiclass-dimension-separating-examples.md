# Separating examples for multiclass learning dimensions

1. (Hexagon class.) Let $H = \{f : \{0,1\} \to \{0,1,2\} : f(0) \ne f(1)\}$, six labelings of two points. Its bipartite graph $G(H)$, with left vertices $\{0,1,2\} \times \{0\}$, right vertices $\{0,1,2\} \times \{1\}$ and an edge $\{(f(0), 0), (f(1), 1)\}$ for each $f \in H$, is a $6$-cycle: it has no leaves and no $4$-cycle, so $H$ is a $2$-dimensional pseudo-cube with Natarajan dimension $1$ (Brukhim, Carmon, Dinur, Moran and Yehudayoff, Example 7). Hence $H$ has Natarajan dimension $1$ and DS dimension $2$, and its graph dimension is $2$, since $\mathrm{DSdim} \le \mathrm{Gdim}$ (Daniely and Shalev-Shwartz, Section 5) and no class on two points has graph dimension above $2$.
2. (Revealing-subset class.) For a set $X$, let $\beta$ be the set of values $\{\bot\} \cup \{\text{finite subsets of } X\}$ and, for each finite $B \subseteq X$, let $r_B(x) = \bot$ for $x \in B$ and $r_B(x) = B$ otherwise. Every value $r_B(x) \ne \bot$ is taken at $x$ by $r_B$ alone, so with $\ast = \bot$ the class $\{r_B\}$ satisfies the hypothesis of Daniely and Shalev-Shwartz, Lemma 20: it has Natarajan dimension at most $1$ and PAC sample complexity at most $\log(1/\delta)/\varepsilon$.

Hence the inequality $\mathrm{Ndim} \le \mathrm{DSdim}$ can be strict.

## Proof sketch

Item 1 is the case of Example 7 in which $G(H)$ is the hexagon $K_{3,3}$ minus a perfect matching. For item 2, if two points were N-shattered by witnesses $f_1, f_2$ with, say, $f_1(x_1) \ne \bot$, the only member taking the value $f_1(x_1)$ at $x_1$ is $f_1$, which cannot also take the value $f_2(x_2) \ne f_1(x_2)$ (proof of Lemma 20).

Derived (not stated in the cited sources): the hexagon class G-shatters both points (take the reference labeling $h = (0, 1)$). The revealing-subset class G-shatters every finite subset of $X$, with the constant reference $\bot$ (for a finite $W \subseteq X$ and $B \subseteq W$, the member $r_B$ equals $\bot$ exactly on $B$ within $W$), so it has infinite graph dimension when $X$ is infinite, while on every nonempty $X$ its DS dimension and Natarajan dimension equal $1$: a non-$\bot$ value identifies $B$, which prevents a two-dimensional pseudo-cube. Hence $\mathrm{DSdim} \le \mathrm{Gdim}$ can be strict too, and over infinite label sets finite DS dimension does not imply finite graph dimension.

## Depends on

- [Natarajan, DS and graph dimensions compared](natarajan-ds-and-graph-dimensions.md)
- [Graph dimension of a multiclass concept class](graph-dimension.md)
- [DS dimension characterizes multiclass PAC learnability](../../ds-dimension-characterizes-multiclass-pac-learnability.md)

## Sources

- A. Daniely and S. Shalev-Shwartz, "Optimal Learners for Multiclass Problems", Proceedings of the 27th Conference on Learning Theory (COLT), 2014, Section 5 and Lemma 20; open copy: <https://arxiv.org/abs/1405.2420>.
- N. Brukhim, D. Carmon, I. Dinur, S. Moran and A. Yehudayoff, "A Characterization of Multiclass Learnability", IEEE 63rd Annual Symposium on Foundations of Computer Science (FOCS), 2022, Definitions 5 and 6 and Example 7; open copy: <https://arxiv.org/abs/2203.01550>.
- S. Ben-David, N. Cesa-Bianchi, D. Haussler and P. M. Long, "Characterizations of Learnability for Classes of {0, ..., n}-Valued Functions", Journal of Computer and System Sciences, 1995.
