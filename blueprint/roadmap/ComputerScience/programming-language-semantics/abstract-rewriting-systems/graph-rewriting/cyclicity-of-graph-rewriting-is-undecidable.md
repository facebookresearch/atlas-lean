# Cyclicity of graph rewriting is undecidable

There is no algorithm that decides, given a graph rewriting system in the double-pushout approach, whether it is cyclic, that is, whether some derivation of the system passes through the same graph twice.

**Theorem.** The following problem is undecidable. Input: a graph rewriting system $\mathcal{G} = \langle \mathcal{C}, \mathcal{R} \rangle$ in the sense of [double-pushout graph rewriting systems](double-pushout-graph-rewriting-systems.md). Question: is $\mathcal{G}$ cyclic, that is, does it admit a derivation $G_0 \Rightarrow_{\mathcal{R}} \cdots \Rightarrow_{\mathcal{R}} G_m$ in which $G_i \cong G_j$ for some $i < j$?

## Depends on

- [Double-pushout graph rewriting systems](double-pushout-graph-rewriting-systems.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The reduction is the one used for [termination](termination-of-graph-rewriting-is-undecidable.md). If the Post instance $L$ has a solution, the derivation of Lemma 3.1 for $\mathcal{G}(L)$ is cyclic. Conversely, a cyclic system is non-terminating, and the argument for termination shows that non-termination of $\mathcal{G}(L)$ yields a solution of $L$. So $\mathcal{G}(L)$ is cyclic exactly when $L$ is solvable.

## Sources

- Detlef Plump, "Termination of graph rewriting is undecidable", *Fundamenta Informaticae* 33(2), 201–209, 1998, <https://doi.org/10.3233/FI-1998-33204>; read as the accepted version, <https://eprints.whiterose.ac.uk/id/eprint/243324/>, which carries the journal's numbering: Theorem 4.1 and the remarks following it.
