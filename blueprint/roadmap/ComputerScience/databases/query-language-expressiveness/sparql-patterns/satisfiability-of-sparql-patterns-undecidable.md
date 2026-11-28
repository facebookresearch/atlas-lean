# Satisfiability of SPARQL patterns is undecidable

A SPARQL graph pattern is satisfiable if some RDF graph gives it a nonempty answer. With AND, UNION, OPTIONAL and FILTER, satisfiability is undecidable once filters may use negated bound-constraints, or both equalities and nonequalities of variables, or equalities with constants.

**Setting (Zhang, Van den Bussche and Picalausa).** Let $I$, $B$ and $L$ be pairwise disjoint infinite sets of IRIs, blank nodes and literals, and $V$ an infinite set of variables disjoint from them. An *RDF graph* is a finite set of triples $(s, p, o)$ whose subject $s$ is an IRI or a blank node, whose predicate $p$ is an IRI and whose object $o$ is an IRI, a blank node or a literal; the *constants* are the IRIs and literals. A *triple pattern* is an element of $(I \cup L \cup V) \times (I \cup V) \times (I \cup L \cup V)$; it contains no blank nodes (blank nodes in patterns can be replaced by variables), and a pattern with a literal in subject position matches nothing. On a graph $G$ a triple pattern $(u, v, w)$ evaluates to the mappings $\mu$ defined exactly on its variables with $(\mu(u), \mu(v), \mu(w)) \in G$, where $\mu$ maps every constant to itself. *Patterns* are built from triple patterns with $P_1 \mathbin{\mathrm{AND}} P_2$, $P_1 \mathbin{\mathrm{UNION}} P_2$, $P_1 \mathbin{\mathrm{OPT}} P_2$ and $P \mathbin{\mathrm{FILTER}} C$, where a filter condition $C$ is $\mathrm{bound}(?x)$, $\neg\mathrm{bound}(?x)$, $?x = ?y$, $?x \neq ?y$ (with $?x$ and $?y$ distinct variables), $?x = c$ or $?x \neq c$ for a constant $c$. Under the set semantics of Arenas, Gutierrez and Pérez, a pattern evaluates on a graph $G$ to a set $[\![P]\!]_G$ of partial mappings from variables: AND joins compatible mappings, UNION takes the union, OPT keeps the join together with the left mappings compatible with no right mapping, and FILTER keeps the mappings satisfying the condition (a comparison involving an unbound variable is not satisfied). For a set $F$ of filter classes among $\mathrm{bound}$, $\neg\mathrm{bound}$, $=$, $\neq$, $=_c$, $\neq_c$, the fragment $\mathrm{SPARQL}(F)$ allows only those filter conditions. A pattern $P$ is *satisfiable* if $[\![P]\!]_G \neq \emptyset$ for some RDF graph $G$.

**Theorem (Zhang, Van den Bussche and Picalausa).** Satisfiability is undecidable for $\mathrm{SPARQL}(\neg\mathrm{bound})$ patterns, for $\mathrm{SPARQL}(=, \neq)$ patterns, and for $\mathrm{SPARQL}(=_c)$ patterns.

These are the three minimal fragments not contained in $\mathrm{SPARQL}(\mathrm{bound}, =, \neq_c)$ or $\mathrm{SPARQL}(\mathrm{bound}, \neq, \neq_c)$, for which the same paper shows satisfiability decidable.

## Depends on

- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

For $\mathrm{SPARQL}(\neg\mathrm{bound})$ the proof reduces from satisfiability of the Downward Algebra, the algebra of finite binary relations over one relation symbol with union, difference and composition, which is undecidable. Fixing an IRI $r$, a binary relation $J$ is represented by the graph $G_J = \{(c, r, d) : (c, d) \in J\}$. By induction, each expression $e$ becomes a pattern $P_e$ whose mappings bind $?x, ?y$ to exactly the pairs of $e(J)$ on $G_J$: $R$ becomes $(?x, r, ?y)$, union becomes UNION, composition joins two translated patterns with AND on a shared middle variable, and $e_1 - e_2$ becomes $(P_{e_1} \mathbin{\mathrm{OPT}} (P_{e_2} \mathbin{\mathrm{AND}} (?u, r, ?w))) \mathbin{\mathrm{FILTER}} \neg\mathrm{bound}(?u)$ with fresh $?u, ?w$. Hence $e$ is satisfiable exactly when $P_e$ is. For $\mathrm{SPARQL}(=, \neq)$, difference is simulated with an OPT whose right side carries a nonequality between two fresh variables, followed by an equality filter on them; $\mathrm{SPARQL}(=_c)$ is handled by a further adaptation.

## Sources

- Xiaowang Zhang, Jan Van den Bussche and François Picalausa, "On the Satisfiability Problem for SPARQL Patterns", Journal of Artificial Intelligence Research 56, pp. 403–428, 2016, <https://doi.org/10.1613/jair.5028>; Section 2 (RDF graphs, syntax and semantics of patterns, fragments) and Theorem 10 (main statement) in Section 4 ("Undecidable fragments") of arXiv:1406.1404v2, read at <https://arxiv.org/abs/1406.1404v2>.
