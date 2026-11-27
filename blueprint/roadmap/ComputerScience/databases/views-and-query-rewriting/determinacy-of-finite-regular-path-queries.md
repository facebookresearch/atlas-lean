# Determinacy of finite regular path queries is undecidable

No algorithm decides, given finitely many finite regular path queries (views) and one more finite regular path query, whether the views determine the query. This holds for finite and for unrestricted determinacy. Finite regular path queries are unions of conjunctive path queries, so undecidability already lives inside positive first-order queries.

**Setting (Głuch, Marcinkowski and Ostropolski-Nalewaja).** A *structure* is a directed graph whose edges carry labels from a finite alphabet $\Sigma$, that is, a relational structure over binary predicates from $\Sigma$; every structure carries two distinguished constants $a$ and $b$. For a word $w = a_1 a_2 \cdots a_n \in \Sigma^\ast$ the *conjunctive path query* $w(v_0, v_n)$ is

$$
\exists v_1, \dots, v_{n-1}\ a_1(v_0, v_1) \wedge a_2(v_1, v_2) \wedge \cdots \wedge a_n(v_{n-1}, v_n).
$$

For a regular language $Q \subseteq \Sigma^\ast$ the *regular path query* $Q$ is $Q(u, v) = \exists w \in Q\ w(u, v)$, and $Q(\mathbb{D})$ is the set of pairs $(u, v)$ of vertices of $\mathbb{D}$ with $\mathbb{D} \models Q(u, v)$. A *finite regular path query* is one whose language $Q$ is finite (a regular expression built from letters with concatenation and union only); it is a union of conjunctive queries. A finite set $\mathcal{Q}$ of queries *determines* a query $Q_0$ if every two structures $\mathbb{D}_1, \mathbb{D}_2$ with $Q(\mathbb{D}_1) = Q(\mathbb{D}_2)$ for all $Q \in \mathcal{Q}$ satisfy $Q_0(\mathbb{D}_1) = Q_0(\mathbb{D}_2)$; in the *finite* version the structures range over finite structures only, in the *unrestricted* version over all structures.

**Theorem (Głuch, Marcinkowski and Ostropolski-Nalewaja).** The following problem is undecidable, both in the finite and in the unrestricted version. Input: an alphabet $\Sigma$, a finite set $\mathcal{Q}$ of finite languages over $\Sigma$ and a finite language $Q_0$ over $\Sigma$. Question: does $\mathcal{Q}$ determine $Q_0$?

The reduction produces only acyclic structures, so the result holds under the simple-path semantics of path queries as well as under the all-paths semantics. It strengthens the earlier undecidability of [determinacy for arbitrary regular path queries](determinacy-of-regular-path-queries-is-undecidable.md) by the same authors. On the positive side, determinacy is decidable when every language in $\mathcal{Q}$ and $Q_0$ consists of a single word (conjunctive path queries, a result of Afrati); the authors note that their result leaves little room for generalizing that positive result.

## Depends on

- [Determinacy of a query by views](determinacy-of-a-query-by-views.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Answers of a conjunctive query](../conjunctive-queries/answers-of-a-conjunctive-query.md)

## Proof depends on

None.

## Expansion

The source of undecidability is recursive inseparability. The sets of Turing machines that, started on the empty tape, return 1 and return 0 are recursively inseparable, and a standard encoding transfers this to a grid tiling problem: an instance is a set of shades containing gray and black and a set of forbidden pairs of shaded edges; let $\mathcal{A}$ be the instances admitting a proper shading of some finite square grid and $\mathcal{B}$ those admitting no proper shading of any square grid, finite or the infinite quarter plane. A computable map sends each instance $I$ to $(\mathcal{Q}, Q_0)$ such that $I \in \mathcal{A}$ implies that $\mathcal{Q}$ does not finitely determine $Q_0$, and $I \in \mathcal{B}$ implies that $\mathcal{Q}$ determines $Q_0$. Since unrestricted determinacy implies finite determinacy, an algorithm for either version would separate $\mathcal{A}$ from $\mathcal{B}$. The correctness of the map rests on a red-green signature and a two-player game of Escape that characterizes determinacy for regular path queries.

A good expansion links the recursive inseparability of the machines returning 1 and returning 0, the recursive inseparability of the two sets of tiling instances, and the lemma that the game of Escape characterizes determinacy; none of them has a page yet.

## Sources

- Grzegorz Głuch, Jerzy Marcinkowski and Piotr Ostropolski-Nalewaja, "The First Order Truth Behind Undecidability of Regular Path Queries Determinacy", 22nd International Conference on Database Theory (ICDT 2019), Leibniz International Proceedings in Informatics (LIPIcs) 127, pp. 15:1–15:18, 2019, <https://doi.org/10.4230/LIPIcs.ICDT.2019.15>. Read in arXiv:1808.07767v2, <https://arxiv.org/abs/1808.07767v2>; Theorem 1.1 (main theorem), Section 3 (preliminaries and notations), Lemma 4.2 (Escape characterizes determinacy), Section 5 (the tiling problem, Lemmas 5.1, 5.2 and 5.3) and the remark on simple-path semantics in Section 1, all in the numbering of arXiv:1808.07767v2.
