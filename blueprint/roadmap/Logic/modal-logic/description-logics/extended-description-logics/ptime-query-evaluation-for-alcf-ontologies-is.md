# PTime query evaluation for ALCF ontologies is undecidable

Unless PTime = NP, no algorithm decides whether a given ontology in the description logic ALCF admits polynomial-time (data complexity) evaluation of conjunctive queries; deciding coNP-hardness of query evaluation and Datalog rewritability is undecidable as well.

**Theorem (Lutz and Wolter).** An *ALCF-TBox* is a finite set of ALC concept inclusions $C \sqsubseteq D$ together with functionality assertions $\mathrm{func}(r)$, satisfied when $r^{\mathcal I}$ is a partial function. An *ABox* is a nonempty finite set of assertions $A(a)$ and $r(a, b)$. For a TBox $\mathcal T$, an ABox $\mathcal A$ and a conjunctive query $q(\vec x)$, a tuple $\vec a$ of individuals of $\mathcal A$ is a *certain answer*, $\mathcal T, \mathcal A \models q(\vec a)$, if $\vec a$ is an answer to $q$ in every model of $\mathcal T$ and $\mathcal A$. The *query evaluation problem* for $(\mathcal T, q(\vec x))$ is to decide, given $\mathcal A$ and $\vec a$, whether $\mathcal T, \mathcal A \models q(\vec a)$; *CQ-evaluation with respect to $\mathcal T$ is in PTime* if this problem is in PTime for every conjunctive query $q(\vec x)$, and *coNP-hard* if it is coNP-hard for some $q(\vec x)$. Then, for ALCF-TBoxes $\mathcal T$, the following problems are undecidable, the first four under the assumption PTime $\neq$ NP (Theorem 7.3 of the source):

1. CQ-evaluation with respect to $\mathcal T$ is in PTime;
2. CQ-evaluation with respect to $\mathcal T$ is coNP-hard;
3. $\mathcal T$ is rewritable into monadic Datalog with inequalities;
4. $\mathcal T$ is rewritable into Datalog with inequalities;
5. $\mathcal T$ is materializable, that is, query evaluation over every ABox with respect to $\mathcal T$ reduces to evaluation in a single model of $\mathcal T$ and the ABox (in the sense of Section 3 of the source).

The source also shows that there is no PTime/coNP dichotomy for query evaluation with respect to ALCF-TBoxes unless PTime = NP: for every language in coNP there is an ALCF-TBox whose query evaluation has the same complexity up to polynomial reductions (Theorem 7.4). By contrast, there is a PTime/coNP dichotomy for query evaluation with respect to ALCFI-TBoxes of depth one and with respect to ALCI-TBoxes (Points 1 and 2 of the source's introduction), the latter through a link to the dichotomy for finite-template constraint satisfaction problems.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../../alc-syntax-semantics-and-reasoning-tasks.md)
- [The class coNP](../../../../TheoryOfComputation/complexity-classes/the-classes-p-np-and-conp/co-np.md)

## Proof depends on

None.

## Expansion

The proofs reduce the finite rectangle tiling problem: given tile types with a horizontal and a vertical matching relation, an initial tile and a final tile, is there a tiling of some rectangle $\{0, \ldots, n\} \times \{0, \ldots, m\}$ with the initial tile in the lower left and the final tile in the upper right corner? From an instance $P$ the source builds an ALCF-TBox $\mathcal T_P$, using functional roles $x, y, \hat x, \hat y$ and "hidden concepts", following a TBox constructed for the undecidability of query emptiness in ALCF, and relates the properties above of the resulting TBoxes to whether $P$ admits a tiling. A good expansion links the undecidability of the finite rectangle tiling problem, which has no page yet.

## Sources

- C. Lutz and F. Wolter, "The data complexity of description logic ontologies", *Logical Methods in Computer Science* 13(4), paper 7, 2017, <https://doi.org/10.23638/LMCS-13(4:7)2017>; read as arXiv:1611.02453v3, <https://arxiv.org/abs/1611.02453v3>: Section 1 (Points 3 and 4 of the results), Section 2 (ALCF-TBoxes, ABoxes, certain answers, Definition 2.3) and Section 7 (the finite rectangle tiling problem, Theorems 7.3 and 7.4).
