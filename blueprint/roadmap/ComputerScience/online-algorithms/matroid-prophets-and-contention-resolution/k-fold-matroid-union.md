# k-fold matroid unions

For a matroid $\mathcal{M} = (E, \mathcal{I})$ and $k \ge 1$, the *$k$-fold union* $\mathcal{M}^{(k)}$ is the matroid union $\mathcal{M} \vee \dots \vee \mathcal{M}$ of $k$ copies of $\mathcal{M}$: the matroid on $E$ whose independent sets are the unions $I_1 \cup \dots \cup I_k$ with $I_j \in \mathcal{I}$, that is, the sets that can be partitioned into $k$ independent sets of $\mathcal{M}$. By Edmonds' matroid union theorem its rank function is $r_k(A) = \min_{B \subseteq A}\big(|A \setminus B| + k\, r(B)\big)$. The $k$-fold union of the rank-one uniform matroid on $E$ is the $k$-uniform matroid on $E$.

## Depends on

- [Matroid union](../../greedy-algorithms-and-matroids/matroid-union-and-p-systems/matroid-union.md)
- [Edmonds' matroid union theorem](../../greedy-algorithms-and-matroids/matroid-union-and-p-systems/matroid-union-rank-formula.md)

## Sources

- Noga Alon, Nick Gravin, Tristan Pollner, Aviad Rubinstein, Hongao Wang, S. Matthew Weinberg, Qianfan Zhang, "A Bicriterion Concentration Inequality and Prophet Inequalities for k-Fold Matroid Unions", ITCS (2025), arXiv:2411.11741, Section 1.
