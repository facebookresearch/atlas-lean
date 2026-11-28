# Conjunctive query entailment over quad-systems with bridge rules is undecidable

Quad-systems attach a context identifier to each RDF triple and propagate knowledge across contexts with bridge rules, existential rules over quad patterns. Entailment of contextualized conjunctive queries over unrestricted quad-systems is undecidable, already with a single context.

**Setting (Joseph, Kuper and Serafini).** RDF constants are URIs, blank nodes and literals. A *quad* $c : (s, p, o)$ is a triple of constants tagged with a context identifier $c$ (a URI); a *quad-graph* is a set of quads. A *bridge rule* is a formula

$$
\forall \vec{x}\, \forall \vec{z}\ \bigl[c_1 : t_1(\vec{x}, \vec{z}) \wedge \dots \wedge c_n : t_n(\vec{x}, \vec{z}) \rightarrow \exists \vec{y}\ c'_1 : t'_1(\vec{x}, \vec{y}) \wedge \dots \wedge c'_m : t'_m(\vec{x}, \vec{y})\bigr]
$$

whose triple patterns $t_i, t'_j$ use variables and constants but no blank nodes. A *quad-system* is a pair $\langle Q, R \rangle$ of a finite quad-graph and a finite set of bridge rules. Its models assign to each context a local interpretation of a fixed local semantics (the source leaves it as a parameter, requiring inference rules whose deductive closure of a finite graph terminates in polynomial time with a result of polynomial size, such as Simple, RDF, RDFS or OWL-Horst, and Theorem 1 holds for whichever is fixed) with rigid constants, satisfying the triples of each context and every bridge rule. A *contextualized conjunctive query* (CCQ) is $\exists \vec{y}\ q_1(\vec{x}, \vec{y}) \wedge \dots \wedge q_p(\vec{x}, \vec{y})$ with quad patterns $q_i$; a tuple $\vec{a}$ is a certain answer if every model satisfies the Boolean query $\mathit{CQ}(\vec{a})$. The *CCQ entailment problem* asks, given a quad-system, a CCQ and a tuple $\vec{a}$, whether $\vec{a}$ is a certain answer.

**Theorem (Joseph, Kuper and Serafini).** The CCQ entailment problem over unrestricted quad-systems is undecidable.

The proof reduces from non-emptiness of the intersection of the languages of two context-free grammars (Theorem 1 of the source), and the quad-systems it produces have a single context, a single quad, and bridge rules whose heads have at most one existential variable. The same paper identifies decidable classes, such as context-acyclic quad-systems, on which the chase terminates.

## Depends on

- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Tuple- and equality-generating dependencies and the chase](../dependencies-and-the-chase/tuple-and-equality-generating-dependencies-and-the-chase.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Whether two context-free languages intersect is undecidable](../../../TheoryOfComputation/undecidable-problems/undecidable-problems-for-context-free-grammars/exists-not-tm2-decidable-overlap.md)

## Expansion

From context-free grammars $G_1, G_2$ over a common terminal set $T$, build a quad-system with one context $c$. Each production $v \to w_1 \cdots w_n$ becomes the rule $c : (x_1, w_1, x_2) \wedge \dots \wedge c : (x_n, w_n, x_{n+1}) \rightarrow c : (x_1, v, x_{n+1})$, each terminal $t \in T$ gives the rule $c : (x, \mathtt{rdf{:}type}, C) \rightarrow \exists y\ c : (x, t, y) \wedge c : (y, \mathtt{rdf{:}type}, C)$, and the quad-graph is the single quad $c : (a, \mathtt{rdf{:}type}, C)$. The terminal rules generate, from $a$, a path for every word over $T$, and the production rules label a path segment by a variable exactly when the variable derives its word. Hence the quad-system entails $\exists y\ c : (a, S_1, y) \wedge c : (a, S_2, y)$ if and only if $L(G_1) \cap L(G_2) \ne \emptyset$.

## Sources

- Mathew Joseph, Gabriel Kuper and Luciano Serafini, "Query Answering over Contextualized RDF/OWL Knowledge with Forall-Existential Bridge Rules: Attaining Decidability Using Acyclicity", Web Reasoning and Rule Systems (RR 2014), Lecture Notes in Computer Science 8741, pp. 60–75, 2014, <https://doi.org/10.1007/978-3-319-11113-1_5>; read in the full version arXiv:1406.0893v1, <https://arxiv.org/abs/1406.0893v1>: the definitions of Section 2 ("Contextualized Quad-Systems"), the CCQ entailment problem and Theorem 1 in Section 3 ("Query Answering on Quad-Systems"), with its proof in the appendix, in the numbering of that version.
