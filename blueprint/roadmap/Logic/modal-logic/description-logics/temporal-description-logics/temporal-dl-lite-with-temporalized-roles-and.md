# Temporal DL-Lite with temporalized roles and next-time is undecidable

Knowledge base satisfiability becomes undecidable for the temporal extension of DL-Lite with full Booleans and number restrictions once roles may be temporalized by "some time" and "always" and concepts may use the next-time operator.

**Theorem (Artale, Kontchakov, Ryzhikov and Zakharyaschev).** Fix concept names $A_i$, local role names $P_i$, rigid role names $G_i$ and object names $a_i$. In the logic $T^{\mathcal R}_{\mathcal X}\textit{DL-Lite}^{\mathcal N}_{bool}$, roles $R$, basic concepts $B$ and concepts $C$ are

$$
S ::= P_i \mid G_i, \qquad R ::= S \mid S^- \mid \Diamond^* R \mid \Box^* R, \qquad B ::= \bot \mid A_i \mid {\ge}\, q\, R, \qquad C ::= B \mid \neg C \mid C_1 \sqcap C_2 \mid \bigcirc_F C,
$$

with $q \ge 1$ a natural number. An interpretation $\mathcal I$ assigns to each time point $n \in \mathbb Z$ an interpretation $\mathcal I(n)$ over one constant domain $\Delta^{\mathcal I}$, with the same interpretation of each object name and of each rigid role name at all time points; as in the source, distinct object names denote distinct elements (the unique name assumption), and the source notes that dropping it changes none of its complexity results except the NLogSpace bound of its Theorem 4 (satisfiability of the core fragment is NLogSpace-complete), which would rise to NP; that bound is not used here, and dropping the assumption changes neither complexity result stated on this page. Then $(S^-)^{\mathcal I(n)}$ is the converse of $S^{\mathcal I(n)}$, $({\ge}\, q\, R)^{\mathcal I(n)}$ is the set of $x$ with at least $q$ elements $y$ such that $(x, y) \in R^{\mathcal I(n)}$, $(\bigcirc_F C)^{\mathcal I(n)} = C^{\mathcal I(n+1)}$, Booleans are as usual, and

$$
(\Diamond^* R)^{\mathcal I(n)} = \bigcup_{k \in \mathbb Z} R^{\mathcal I(k)}, \qquad (\Box^* R)^{\mathcal I(n)} = \bigcap_{k \in \mathbb Z} R^{\mathcal I(k)} .
$$

A TBox is a finite set of concept inclusions $C_1 \sqsubseteq C_2$, satisfied when $C_1^{\mathcal I(n)} \subseteq C_2^{\mathcal I(n)}$ for all $n \in \mathbb Z$; an ABox is a finite set of assertions $\bigcirc^n B(a)$ and $\bigcirc^n S(a, b)$ with $n \in \mathbb Z$, saying that $a^{\mathcal I} \in B^{\mathcal I(n)}$, respectively $(a^{\mathcal I}, b^{\mathcal I}) \in S^{\mathcal I(n)}$; a knowledge base is a TBox with an ABox, and it is satisfiable if it has a model. The satisfiability problem for $T^{\mathcal R}_{\mathcal X}\textit{DL-Lite}^{\mathcal N}_{bool}$ knowledge bases is undecidable (Theorem 5 of the source).

The source attributes the undecidability to the interaction of functionality constraints on temporalized roles with the next-time operator and full Booleans on concepts. Without temporalized roles, satisfiability of knowledge bases of the full temporal language with until and since on concepts and rigid roles is PSPACE-complete (Theorem 1 of the source).

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof reduces the problem whether a finite set of tile types tiles the grid $\mathbb N \times \mathbb N$. Time gives one axis of the grid. Inclusions such as ${\ge}\,2\,\Diamond^* R \sqsubseteq \bot$ and ${\ge}\,2\,\Diamond^* R^- \sqsubseteq \bot$ make $R$ injective across all time points, and inclusions using $\bigcirc_F$ generate an $R$-chain of domain elements, the other axis; columns of tiles are placed every $k + 1$ moments, with $k$ the number of colors, and their colors are matched by further inclusions. The knowledge base is satisfiable iff the tile set tiles $\mathbb N \times \mathbb N$. The undecidability of tiling the quadrant $\mathbb N \times \mathbb N$, which the source cites from Börger, Grädel and Gurevich, is equivalent by compactness to the undecidability of tiling the plane.

## Sources

- A. Artale, R. Kontchakov, V. Ryzhikov and M. Zakharyaschev, "Past and future of DL-Lite", in *Proceedings of the Twenty-Fourth AAAI Conference on Artificial Intelligence (AAAI 2010)*, AAAI Press, 2010, pp. 243–248, <https://doi.org/10.1609/aaai.v24i1.7580>; read in the open-access author copy at <http://titan.dcs.bbk.ac.uk/~roman/papers/aaai10-final.pdf>: the section introducing the temporal DL-Lite languages (syntax, semantics, knowledge bases, Theorem 1) and the section on logics with temporalized roles (Theorem 5 and its proof).
