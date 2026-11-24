# The Čech complex of a presheaf

Let $\mathcal{C}$ be a category with finite products, $\mathcal{A}$ a preadditive category with
products and $(U_i)_{i \in I}$ a family of objects of $\mathcal{C}$. The Čech complex of a presheaf
$P \colon \mathcal{C}^{\mathrm{op}} \to \mathcal{A}$ for this family is the cochain complex, in
degrees $n \ge 0$,

$$C^n = \prod_{(i_0, \dots, i_n) \in I^{n+1}} P(U_{i_0} \times \dots \times U_{i_n}),$$

with the differential $d = \sum_{k = 0}^{n + 1} (-1)^k d_k \colon C^n \to C^{n+1}$, where $d_k$ is
induced by the projections of $U_{i_0} \times \dots \times U_{i_{n+1}}$ that omit the factor
$U_{i_k}$; it is functorial in $P$. For the open subsets of a topological space, ordered by
inclusion, these products are the intersections $U_{i_0} \cap \dots \cap U_{i_n}$, and this is the
Čech complex of a presheaf for an open covering.

## Sources

- The Stacks Project, Section 20.9, <https://stacks.math.columbia.edu/tag/01ED>: the Čech complex of
  a presheaf of abelian groups for an open covering.
