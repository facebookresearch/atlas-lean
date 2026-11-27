# Local first-order logic with two data values is undecidable at radius 3

Satisfiability of local first-order logic over data structures with two data values per node is undecidable when the local views have radius 3, and also at radius 2 once one diagonal comparison between data values is allowed.

**Theorem (Bollig, Sangnier and Stietel).** For [local first-order logic with data](local-first-order-logic-with-data.md):

1. $\mathrm{DataSat}(3\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 2, \{{}_1{\sim}_1, {}_2{\sim}_2\})$ is undecidable (Theorem 3.26);
2. $\mathrm{DataSat}(2\text{-}\mathrm{Loc}\text{-}\mathrm{dFO}, 2, \{{}_1{\sim}_1, {}_2{\sim}_2, {}_1{\sim}_2\})$ is undecidable (Theorem 3.30).

That is, there is no algorithm that decides, given a finite set $\Sigma$ and a sentence of the local logic of radius $3$ (respectively $2$) over finite $2$-data structures with the stated comparison symbols, whether some finite $2$-data structure over $\Sigma$ satisfies it. With radius $1$ and $\{{}_1{\sim}_1, {}_2{\sim}_2, {}_1{\sim}_2\}$, satisfiability is decidable (Theorem 3.20).

## Depends on

- [Local first-order logic with data](local-first-order-logic-with-data.md)

## Proof depends on

None.

## Expansion

Both parts reduce the periodic tiling problem Tiles: does a domino system admit a periodic tiling, a tiling of some torus $G_m$? A formula of the local logic, built with the help of Otto's characterization of grid-like bi-binary structures (Lemma 3.21), forces the models to contain tori: the horizontal and vertical neighbor relations are defined from shared first and second data values, and the formulas $\varphi_{\mathrm{complete}}$ and $\varphi_{\mathrm{progress}}$ that make the structure grid-like are expressible within views of radius $3$. A domino system admits a periodic tiling iff the corresponding sentence is satisfiable (Proposition 3.25). For radius $2$, the diagonal relation ${}_1{\sim}_2$ supplies the diagonal adjacency needed to express completeness of squares within smaller views (Lemmas 3.27 and 3.28, Proposition 3.29).

## Sources

- B. Bollig, A. Sangnier and O. Stietel, "On the Satisfiability of Local First-Order Logics with Data", *Logical Methods in Computer Science* 20(3), 2024, paper 1, pp. 1:1–1:42, <https://doi.org/10.46298/lmcs-20(3:1)2024>; numbers from arXiv:2307.00831v4, <https://arxiv.org/abs/2307.00831v4>: Section 3: Theorem 3.20, Lemma 3.21, Proposition 3.25, Theorem 3.26, Lemmas 3.27 and 3.28, Proposition 3.29 and Theorem 3.30.
