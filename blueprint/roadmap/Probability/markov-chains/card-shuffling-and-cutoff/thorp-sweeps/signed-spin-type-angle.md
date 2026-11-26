# One-sided angles for signed spin types on occupied boards

Let $R,C$ be finite sets, $W\subseteq R\times C$, and $q\ge1$. On $(\mathbb C^q\oplus\mathbb C^q)^{\otimes W}$ use the independent unitary group action $U(q)\times U(q)$ in the two blocks. A type $D=(D_e,D_o)$ consists of two Young diagrams of height at most $q$. The polynomial representation for each diagram is the cyclic span of the column-alternated tensor whose color is the row index, acted on by the same $U(q)$ at all cells. The type representation is the external tensor product of the two polynomial representations. Define $P_D$ as the orthogonal projection onto the span of images of intertwiners of that type into the signed tensor action. Write $s_D$ for its total number of cells, $\dim_D$ for the dimension of the type representation, and $E_D=s_D\log s_D-\sum_a a\log a$ for the sum over all row lengths of both diagrams, with $0\log0=0$.

Choose global type $D$ of size $|W|$, column types $H_j$ whose sizes match the corresponding occupied columns, and row types $K_i$ whose sizes match the occupied rows. Write $P_H,P_K$ for the tensor products of their respective fiber projections, $E_H,E_K$ for sums of type entropies, and $\dim_H,\dim_K$ for products of type dimensions. Put $M=|C|$ and $b_i=M-|\{j:(i,j)\in W\}|$. The missing-cell factor is $\varphi=\prod_{i:b_i<M}(M/(M-b_i))^{M-b_i}$ (factor one for an empty row). The conclusions are

$$
\|P_H P_K P_D\|_{2\to2}^2\ \le\ \min(1,e^{E_H+E_K-E_D}\dim_H\dim_K\varphi)\ \le\ \min(1,e^{E_H+E_K-E_D+|R||C|-|W|}\dim_H\dim_K)
$$

and $\dim_H\dim_K\le(|W|+1)^{(|R|+|C|)q(q-1)}$.

**Conventions.** Use the tensor-product signed action, cyclic column-alternating polynomial carriers and their isotypic projections, fiber tensor regrouping, and the entropy and empty-row conventions.

## Depends on

The statement uses the explicit definitions given above.

## Expansion

The one-sided compression comparison in signed tensor space, and a Young-type dimension estimate with the explicit height and board sizes.

Establish orthogonal projection semantics and type dimension in the native representation API. Isolate the occupied-to-full-board comparison, the elementary estimate $\varphi\le e^{|R||C|-|W|}$, and the representation-theoretic dimension bound. The order of the factors is column times row times global (the global projection acts first).

## Sources

- [Pinned source statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SpinAngle.lean#L521-L537)
- [Scope of the source formalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/238.md)
- [Accompanying manuscript: Signed tensor densities and diagram budgets for the Thorp shuffle](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Signed-tensor-densities-and-diagram-budgets-for-coordinate-sweeps-September-26-2026/paper.pdf)
- [Pinned definitions used inline](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SpinAngle.lean#L11-L519)
