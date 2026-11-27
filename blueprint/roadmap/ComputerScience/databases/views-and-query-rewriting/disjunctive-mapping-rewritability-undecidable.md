# Disjunctive mapping rewritability is undecidable

It is undecidable whether a union of conjunctive queries over a target schema, together with a disjunctive mapping from a source schema, has a finite complete rewriting as a union of conjunctive queries over the source. The mappings built in the proof are disjunctive datalog: their rules have no existential variables.

**Theorem.** Disjunctive mapping rewritability is undecidable: there is no algorithm that, given disjoint sets of source predicates $\mathcal{S}$ and target predicates $\mathcal{T}$, a disjunctive mapping $\mathcal{M}$ on $(\mathcal{S}, \mathcal{T})$ and a UCQ $\mathcal{Q}$ over $\mathcal{T}$, decides whether $(\mathcal{Q}, \mathcal{M})$ has a UCQ-$\mathcal{S}$-rewriting, in the sense of [Disjunctive mappings and UCQ rewritings over the source](disjunctive-mappings-and-source-rewritings.md).

## Depends on

- [Disjunctive mappings and UCQ rewritings over the source](disjunctive-mappings-and-source-rewritings.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof reduces from UCQ-rewritability of a Boolean CQ $Q$ with a set $\mathcal{R}$ of conjunctive datalog rules over predicates $\mathcal{P}$, assumed without constants and with atomic heads. That problem is undecidable because a datalog program is uniformly bounded exactly when $(Q, \mathcal{R})$ is UCQ-rewritable for every atomic query $Q$ all of whose variables are answer variables, there are finitely many such atomic queries up to isomorphism, and an answer atom over all variables turns an atomic query into a Boolean CQ; uniform boundedness of datalog programs is undecidable by Gaifman, Mairson, Sagiv and Vardi.

The reduction takes $\mathcal{S} = \mathcal{P} \cup \{T\}$ with a fresh unary $T$, and lets $\mathcal{T}$ contain a hatted copy $\hat{p}$ of each predicate of $\mathcal{S}$ and a fresh predicate $p_{R_i}$, of arity the frontier size, for each rule $R_i = B_i[\vec{x}_i, \vec{y}_i] \rightarrow H_i[\vec{x}_i]$. The mapping copies every source predicate, $p(\vec{x}) \rightarrow \hat{p}(\vec{x})$, and adds for each rule

$$
T(x_1) \wedge \dots \wedge T(x_k) \rightarrow p_{R_i}(\vec{x}_i) \vee \hat{H}_i(\vec{x}_i), \quad \vec{x}_i = (x_1, \dots, x_k).
$$

The UCQ contains the hatted copy of $Q$ with a $\hat{T}$ atom on each variable, and for each rule the CQ $\hat{B}_i[\vec{x}_i, \vec{y}_i] \wedge p_{R_i}(\vec{x}_i)$ with $\hat{T}$ atoms on all its variables. The source shows that $(Q, \mathcal{R})$ is UCQ-rewritable if and only if the constructed pair has a UCQ-$\mathcal{S}$-rewriting.

A good expansion links the undecidability of uniform boundedness of datalog programs (Gaifman, Mairson, Sagiv and Vardi), where uniform boundedness is boundedness over input databases that may also contain facts of the intensional predicates, and the equivalence between uniform boundedness and UCQ-rewritability of all atomic queries.

## Sources

- Michel Leclère, Marie-Laure Mugnier and Guillaume Pérution-Kihli, "Query Rewriting with Disjunctive Existential Rules and Mappings", in *Proceedings of the 20th International Conference on Principles of Knowledge Representation and Reasoning (KR 2023)*, pp. 429–439, 2023, <https://doi.org/10.24963/kr.2023/42>; read in arXiv:2306.05973v1, <https://arxiv.org/abs/2306.05973v1>: Theorem 6 (Section 5) with its proof sketch and the full proof in the appendix of that version.
- Haim Gaifman, Harry Mairson, Yehoshua Sagiv and Moshe Y. Vardi, "Undecidable optimization problems for database logic programs", *Journal of the ACM* 40(3):683–713, 1993, <https://doi.org/10.1145/174130.174142>, for the undecidability of uniform boundedness used in the proof (cited, not read).
