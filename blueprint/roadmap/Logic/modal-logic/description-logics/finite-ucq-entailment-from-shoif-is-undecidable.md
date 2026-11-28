# Finite entailment of unions of conjunctive queries from SHOIF knowledge bases is undecidable

Whether a union of conjunctive queries holds in every finite model of a knowledge base of the expressive description logic SHOIF is undecidable, and so are finite conjunctive query entailment for SROIF⁻ and finite entailment of two-way regular path queries for ALCOIF.

**Logics.** ALCOIF extends [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md) by nominals $\{a\}$, inverse roles $r^-$ and functionality axioms $\mathrm{Fun}(r)$, satisfied when $r^{\mathcal{I}}$ is a partial function. SHOIF partitions the role names into *simple* and *non-simple* roles (an inverse role $r^-$ has the kind of $r$, as the source's own axioms such as $\mathrm{Fun}(\mathit{next}^-)$ use) and adds role inclusions $s \sqsubseteq r$, where $r$ must be non-simple whenever $s$ is, and transitivity axioms $\mathrm{Trans}(r)$; functionality axioms $\mathrm{Fun}(s)$ are allowed only for simple roles $s$ and transitivity axioms $\mathrm{Trans}(r)$ only for non-simple roles $r$. SROIF⁻ further allows complex role inclusions $r_1 \circ \cdots \circ r_n \sqsubseteq r$ under the usual global restrictions: the *simplicity* constraint, that $r$ is non-simple if $n > 1$, or if $n = 1$ and $r_1$ is non-simple; and the *regularity* constraint, that some strict partial order $\prec$ on roles, with $s \prec r$ iff $\mathrm{Inv}(s) \prec r$, makes every role inclusion take one of the forms $r \circ r \sqsubseteq r$, $\mathrm{Inv}(r) \sqsubseteq r$, $r_1 \circ \cdots \circ r_n \sqsubseteq r$, $r \circ r_1 \circ \cdots \circ r_n \sqsubseteq r$ or $r_1 \circ \cdots \circ r_n \circ r \sqsubseteq r$ with $r_i \prec r$ for all $i$ (Section "Finite CQ Entailment in SROIF⁻" of the KR 2016 paper). A knowledge base is a finite set of such axioms together with concept inclusions and assertions.

**Queries and finite entailment.** A conjunctive query is a finite set of atoms $A(x)$ and $r(x, y)$ over variables, all existentially quantified (Boolean queries, as in the source's footnote on query entailment), which holds in an interpretation if some assignment of domain elements to its variables makes all atoms true; a union of conjunctive queries holds if one of them does. A two-way regular path query $E(x, y)$ asks for a path from $x$ to $y$ whose sequence of roles and inverse roles matches the regular expression $E$. A knowledge base $\mathcal{K}$ *finitely entails* a query $q$, written $\mathcal{K} \models_{\mathrm{fin}} q$, if $q$ holds in every model of $\mathcal{K}$ with a finite domain.

**Theorem (Rudolph).**

1. Finite entailment of unions of conjunctive queries from SHOIF knowledge bases is undecidable (Corollary 11 of the KR 2016 paper; Corollary 1 of the DL 2016 copy).
2. Finite entailment of conjunctive queries from SROIF⁻ knowledge bases is undecidable (Corollary 13 of the KR 2016 paper; Corollary 2 of the DL 2016 copy).
3. Finite entailment of two-way regular path queries from ALCOIF knowledge bases is undecidable (Corollary 16 of the KR 2016 paper; Corollary 3 of the DL 2016 copy).

Finite and unrestricted entailment differ: the SHOIF knowledge base with $\mathrm{Fun}(r^-)$, $\top \sqsubseteq \exists r.\top$, $r \sqsubseteq r'$ and $\mathrm{Trans}(r')$ does not entail $r'(x, x)$, but finitely entails it.

## Depends on

- [ALC syntax, semantics and reasoning tasks](../alc-syntax-semantics-and-reasoning-tasks.md)
- [Answers of a conjunctive query](../../../ComputerScience/databases/conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable over the binary alphabet](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/not-tm2-decidable-pcp-bool.md)

## Expansion

For a PCP instance $P$, a finite list of pairs of nonempty words over the two-letter alphabet $\{a, b\}$ (Definition 3 of the KR 2016 paper; Definition 2 of the DL 2016 copy), a SHOIF knowledge base $\mathcal{K}_P$ has finite models that spell a candidate solution letter by letter along a chain, with a correspondence relation between the two spelled words, and two conjunctive queries $q_1, q_2$ are matched exactly in the finite models that do not encode a solution; then $P$ has a solution iff $\mathcal{K}_P \not\models_{\mathrm{fin}} \{q_1, q_2\}$ (Theorem 10 of the KR 2016 paper; Theorem 2 of the DL 2016 copy). Complex role inclusions merge the two queries into one, and a reduction of the source turns the one-atom query into a two-way regular path query over ALCOIF. The reduction starts from PCP over $\{a, b\}$ restricted to pairs of non-empty words, as in Definition 2; a good expansion links the undecidability of that restriction, which the linked undecidability of PCP over a two-letter alphabet, whose instances may contain empty words, does not give by itself.

## Sources

- S. Rudolph, "Undecidability results for database-inspired reasoning problems in very expressive description logics", in *Principles of Knowledge Representation and Reasoning: Proceedings of the 15th International Conference (KR 2016)*, AAAI Press, 2016, pp. 247–256; read in the author's copy at [iccl.inf.tu-dresden.de copy](https://iccl.inf.tu-dresden.de/w/images/7/79/KR16-Rudolph.pdf): the preliminaries on SHOIF (simple and non-simple roles), Definition 3, Theorem 10, Corollaries 11, 13 and 16, and the global restrictions of the section "Finite CQ Entailment in SROIF⁻".
- S. Rudolph, "The curse of finiteness: undecidability of database-inspired reasoning problems in very expressive description logics", in *Proceedings of the 29th International Workshop on Description Logics (DL 2016)*, CEUR Workshop Proceedings 1577, 2016, paper 12; read in the open-access copy at [iccl.inf.tu-dresden.de copy](https://iccl.inf.tu-dresden.de/w/images/b/be/DL16-curse-of-finiteness.pdf): the preliminaries (Definition 1, Examples 1 and 2), Theorem 2 and Corollaries 1–3.
