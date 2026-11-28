# Termination of graph rewriting is undecidable

There is no algorithm that decides, given a graph rewriting system in the double-pushout approach (a finite label alphabet and a finite set of rules), whether the system is terminating, that is, whether no infinite derivation of finite graphs exists.

**Theorem.** The following problem is undecidable. Input: a graph rewriting system $\mathcal{G} = \langle \mathcal{C}, \mathcal{R} \rangle$ in the sense of [double-pushout graph rewriting systems](double-pushout-graph-rewriting-systems.md), with the label alphabet $\mathcal{C}$ and the finite rule set $\mathcal{R}$ both part of the input. Question: is $\mathcal{G}$ terminating, that is, is there no infinite derivation $G_0 \Rightarrow_{\mathcal{R}} G_1 \Rightarrow_{\mathcal{R}} \cdots$ from any finite graph $G_0$ over $\mathcal{C}$?

## Depends on

- [Double-pushout graph rewriting systems](double-pushout-graph-rewriting-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem. For an instance $L = \langle (u_1, v_1), \dots, (u_n, v_n) \rangle$ in which no pair has both words empty (a restriction under which the problem stays undecidable) one builds a system $\mathcal{G}(L)$ whose edge labels are the letters of the instance, the indices $1, \dots, n$ and three markers, and whose rules fall into four groups $\mathcal{R}_1, \dots, \mathcal{R}_4$; each rule has exactly one control node (a vertex labeled $l$ or $r$) on each side. If $L$ has a solution, $\mathcal{G}(L)$ admits a cyclic, hence infinite, derivation (Lemma 3.1). Conversely, every infinite derivation applies the single rule of $\mathcal{R}_4$ infinitely often at one control node (Lemma 3.2), a derivation from a connected graph keeps exactly one control node (Lemma 3.3), and between consecutive applications of $\mathcal{R}_4$ the shape of the rules forces the words written beside the control node to satisfy $u_{i_1} \cdots u_{i_k} = v_{i_1} \cdots v_{i_k}$ with $k \ge 1$ (Lemma 3.4). Hence $\mathcal{G}(L)$ is non-terminating exactly when $L$ has a solution.

Termination cannot be reduced more directly from string rewriting or Turing machines: the translation of the terminating string rule $ab \to ba$ into a graph rule is non-terminating on a cyclic graph, and graph rules cannot copy subgraphs as non-linear term rules do. A good expansion links pages for Lemmas 3.1 to 3.3 of the source and for the undecidability of the Post correspondence problem restricted to instances in which no pair has both words empty.

## Sources

- Detlef Plump, "Termination of graph rewriting is undecidable", *Fundamenta Informaticae* 33(2), 201–209, 1998, <https://doi.org/10.3233/FI-1998-33204>; read as the accepted version, <https://eprints.whiterose.ac.uk/id/eprint/243324/>, which carries the journal's numbering: Theorem 3.1 and its proof (Lemmas 3.1–3.4).
