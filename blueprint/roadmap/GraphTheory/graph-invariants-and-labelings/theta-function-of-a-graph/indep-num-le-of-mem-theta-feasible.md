# Every feasible value dominates the independence number

For a finite graph $G$, every [feasible value](theta-feasible.md) $t$ of the theta program satisfies $\alpha(G) \le t$. If $a$ and $c$ witness $t$ and $S$ is a maximum stable set, then

$$
|S| = \sum_{v \in S} 1 \le t \sum_{v \in S} \mathrm{cost}_c(a_v) \le t ,
$$

because [stable sets have total cost at most one](sum-cost-le-one.md).

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, eq. (4.9) and Lemma 1.
