# Theta body

For a finite graph $G$ on $V$, the theta body of Grötschel, Lovász and Schrijver is

$$
\mathrm{TH}(G) = \Bigl\{x \in \mathbb{R}^V : x \ge 0,\ \sum_{v} \mathrm{cost}_c(a_v)\, x_v \le 1 \text{ for every orthogonal labeling } a \text{ of } G \text{ and every handle } c\Bigr\},
$$

where labelings take values in any $\mathbb{R}^d$. It is convex but in general not a polytope; it lies between $\mathrm{STAB}(G)$ and $\mathrm{QSTAB}(G)$, and the maximum of $\sum_v x_v$ over it is $\vartheta(G)$ ([theta as a maximum over the theta body](lovasz-theta-eq-s-sup-th.md)). Knuth fixes the handle to the first coordinate vector; by an orthogonal change of coordinates (his Lemma 0) the two definitions give the same set.

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, §2 (where $\mathrm{TH}$ is credited to Grötschel, Lovász and Schrijver).
