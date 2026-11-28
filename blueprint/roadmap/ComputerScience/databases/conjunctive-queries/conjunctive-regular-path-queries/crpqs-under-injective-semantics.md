# Conjunctive regular path queries under injective semantics

A conjunctive regular path query joins atoms that ask for paths with labels in regular languages; under atom-injective semantics each such path must be simple, and under query-injective semantics the whole match must moreover be injective with internally disjoint paths.

**Graph databases and paths.** A *graph database* over a finite alphabet $\mathbb A$ is a finite edge-labeled graph $G = (V, E)$ with $E \subseteq V \times \mathbb A \times V$. A *path* from $u$ to $v$ is a possibly empty sequence of edges $v_0 \xrightarrow{a_1} v_1, \dots, v_{k-1} \xrightarrow{a_k} v_k$ with $v_0 = u$, $v_k = v$; its label is $a_1 \cdots a_k$ ($\epsilon$ when $k = 0$). It is a *simple path* if $v_0, \dots, v_k$ are pairwise distinct and a *simple cycle* if $v_0 = v_k$ and $v_0, \dots, v_{k-1}$ are pairwise distinct; $v_1, \dots, v_{k-1}$ are its internal nodes.

**Queries.** A *conjunctive regular path query* (CRPQ) over $\mathbb A$ is an expression $Q(\bar z) = x_1 \xrightarrow{L_1} y_1 \land \cdots \land x_n \xrightarrow{L_n} y_n$ with variables $x_i, y_i$, regular expressions $L_i$ over $\mathbb A$ and a tuple $\bar z$ of (not necessarily distinct) free variables; the other variables are existentially quantified. A conjunctive query (CQ) is a CRPQ whose expressions are single letters. $\mathrm{CRPQ}^{\mathrm{fin}}$ is the class of CRPQs whose expressions contain no Kleene star, hence denote finite languages.

**Semantics.** Suppose first that no $L_i$ contains $\epsilon$. The evaluation $Q(G)^{st}$ under *standard semantics* is the set of tuples $\mu(\bar z)$ for mappings $\mu$ from the variables of $Q$ to $V$ such that for each $i$ some path $\pi_i$ from $\mu(x_i)$ to $\mu(y_i)$ has its label in $L_i$. Under *atom-injective semantics*, $Q(G)^{a\text{-}inj}$, each $\pi_i$ must in addition be a simple path if $x_i \ne y_i$ and a simple cycle if $x_i = y_i$. Under *query-injective semantics*, $Q(G)^{q\text{-}inj}$, the $\pi_i$ must be simple in this sense, $\mu$ must be injective, and no two distinct paths $\pi_i$, $\pi_j$ may share an internal node. If some $L$ in an atom $x \xrightarrow{L} y$ contains $\epsilon$, the evaluation is the union of the evaluation with $L \setminus \{\epsilon\}$ and the evaluation of the query obtained by deleting the atom and substituting $y$ for $x$.

**Containment.** For a semantics $\star$, $Q_1 \subseteq_\star Q_2$ if $Q_1(G)^\star \subseteq Q_2(G)^\star$ for every graph database $G$. For classes $\mathcal C_1, \mathcal C_2$ of CRPQs, the $\mathcal C_1/\mathcal C_2$ containment problem under $\star$-semantics asks, given $Q_1 \in \mathcal C_1$ and $Q_2 \in \mathcal C_2$, whether $Q_1 \subseteq_\star Q_2$.

## Depends on

- [Answers of a conjunctive query](../answers-of-a-conjunctive-query.md)
- [Language denoted by a regular expression](../../../../TheoryOfComputation/regular-languages/automata-and-expressions/kleene-s-theorem/is-regex-denoted.md)

## Proof depends on

None.

## Expansion

The three semantics form a hierarchy: $Q(G)^{q\text{-}inj} \subseteq Q(G)^{a\text{-}inj} \subseteq Q(G)^{st}$ for every $Q$ and $G$, and the inclusions are strict in general. Atom-injective semantics extends the simple-path semantics of regular path queries atom by atom (with nodes and edges exchanged, it is the semantics used by the Neo4j query language). Under standard semantics, CRPQ/CRPQ containment is EXPSPACE-complete, by results of Calvanese, De Giacomo, Lenzerini and Vardi and of Florescu, Levy and Suciu.

## Sources

- Diego Figueira and Miguel Romero, "Conjunctive Regular Path Queries under Injective Semantics", in *Proceedings of the 42nd ACM SIGMOD-SIGACT-SIGAI Symposium on Principles of Database Systems (PODS 2023)*, ACM, 2023, pp. 231–240, <https://doi.org/10.1145/3584372.3588664>; read as arXiv:2304.06232v1, <https://arxiv.org/abs/2304.06232v1>: Section 2 (preliminaries: graph databases and CRPQs) with Section 2.1 (standard, atom-injective and query-injective semantics), and the containment problem in Section 4, in the numbering of that version.
