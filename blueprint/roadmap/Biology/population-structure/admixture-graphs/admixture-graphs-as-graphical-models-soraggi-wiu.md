# Single-root stochastic admixture graphs realize the drift model

Let $G$ be a finite single-root [admixture graph](admixture-graph.md)
with proportions $a(j,i)$ from parent $i$ into node $j$.
Take a square-integrable root $V_\rho$. In an acyclic order, sample a
square-integrable contribution $C_{ij}$ for each edge $i\to j$ from a
kernel depending only on $V_i$, using fresh independent randomness,
and set $V_j=\sum_{i\in\operatorname{pa}(j)}a(j,i)C_{ij}$.
Assume each contribution kernel has conditional mean $V_i$.
Equivalently for this construction, before sampling edge $e=(i,j)$,
$\mathbb E[C_{ij}\mid\mathcal H_{e-}]=V_i$, where $\mathcal H_{e-}$
contains the root and all previously generated variables.
With $d_{ij}=C_{ij}-V_i$ and $\ell_{ij}=\mathbb E d_{ij}^2$,

$$\mathbb E d_e=0,\quad \mathbb E(d_ed_f)=0\ (e\ne f),\quad
 \ell_{ij}=\operatorname{Var}(C_{ij})-\operatorname{Var}(V_i),\qquad
 V_j=V_\rho+\sum_e w(j,e)d_e.$$

Here $w(j,e)$ is the sum of products of proportions over root-to-$j$
paths containing $e$, exactly the canonical lineage weight. Hence these
variables realize the [drift model](../patterson-s-f-statistics/drift-model.md).
For any nodes $i,j$, subtracting gives
$V_j-V_i=\sum_e(w(j,e)-w(i,e))d_e$ and thus the canonical f-statistic
formulas, including $f_2(i,j)=\sum_e(w(j,e)-w(i,e))^2\ell_e$.

## Depends on

- [Admixture graph and proportions](admixture-graph.md)
- [Canonical second-moment drift model](../patterson-s-f-statistics/drift-model.md)

## Expansion

Each new $d_e$ has conditional mean zero given all earlier variables,
so it is orthogonal to them, including every earlier $d_f$ and the root.
Cauchy–Schwarz ensures products are integrable. In particular
$\mathbb E(C_{ij}V_i)=\mathbb E V_i^2$ and
$\mathbb E C_{ij}=\mathbb E V_i$, which proves the variance difference.
Inductively expand $V_j=\sum_i a(j,i)(V_i+d_{ij})$.
The coefficients are products along paths; the root coefficient is one
because incoming proportions sum to one. This proves the representation
and the difference formula without requiring mutually independent drifts.

There is also a weaker second-moment version. If a node model is given by
$V_j=\sum_i a(j,i)V_i+\varepsilon_j$, where the square-integrable
innovations have mean zero, are pairwise orthogonal and are orthogonal
to the root, insert a noiseless mixing node $j_0$ followed by the edge
$j_0\to j$ carrying $\varepsilon_j$. This expanded graph has the same
frequencies and canonical second-moment representation. This algebraic
version does not infer kernel independence from orthogonality alone.
For a diamond with root-to-parent drifts $u,v$, an admixture proportion
$\alpha$ and child drift $z$, the terminal frequency is
$V_\rho+\alpha u+(1-\alpha)v+z$, with root-to-terminal second moment
$\alpha^2\mathbb E u^2+(1-\alpha)^2\mathbb E v^2+\mathbb E z^2$.

The full multi-root chain-graph model, its signed undirected root edges
and its root-martingale characterization require separate contracts.
They are not silently identified with this single-root canonical graph.

## Sources

- S. Soraggi and C. Wiuf, *General theory for stochastic admixture graphs and F-statistics* (2019), <https://doi.org/10.1016/j.tpb.2018.12.002>, <https://arxiv.org/abs/1807.07593>, Definition 5, Theorem 3 and Lemma 1. The single-root generative hypotheses and the node-innovation expansion are explicit here. The variance identity uses the directly derived positive identity $\mathbb E(C_{ij}V_i)=\mathbb E V_i^2$.
