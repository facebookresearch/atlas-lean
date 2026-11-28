# Having an existential local equivalent over finite structures is undecidable

Over finite structures, no algorithm decides whether a first-order sentence closed under disjoint unions is equivalent to an existential local sentence, the existential closure of a formula that only speaks about a bounded neighbourhood of its free variables.

**Setting.** For a finite relational signature $\sigma$, the Gaifman graph of a $\sigma$-structure joins two elements that occur together in a tuple of some relation, and $d(x, y)$ is the distance in it. A formula $\tau(\vec{x})$ is *$r$-local* if its quantifiers are relativised to the elements at distance at most $r$ from $\vec{x}$. An *existential local sentence* is a sentence $\exists \vec{x}.\, \tau(\vec{x})$ with $\tau$ an $r$-local formula for some $r$; these sentences are exactly as expressive as positive Boolean combinations of basic local sentences $\exists \vec{x}.\, \bigwedge_{i \ne j} d(x_i, x_j) > 2r \wedge \bigwedge_i \psi_{\le r}(x_i)$. $\mathrm{Fin}(\sigma)$ is the class of finite $\sigma$-structures. A sentence $\varphi$ is *closed under disjoint unions* over $\mathrm{Fin}(\sigma)$ if for every finite model $A$ of $\varphi$ and every $B \in \mathrm{Fin}(\sigma)$, the disjoint union $A \uplus B$ is again a model of $\varphi$ (Section 1.1.4 of the source); by Lemma 2.5 of the source this is preservation under local elementary embeddings over $\mathrm{Fin}(\sigma)$. For instance $\forall x\, E(x, x)$ is not closed under disjoint unions, since adding a point without a loop gives a structure that is not a model.

**Theorem (Lopez).** It is in general not possible to decide whether a first-order sentence $\varphi$ closed under disjoint unions over $\mathrm{Fin}(\sigma)$ is equivalent over $\mathrm{Fin}(\sigma)$ to an existential local sentence: there is a finite relational signature $\sigma$, the one used in the source's reduction, for which no algorithm decides this for given $\varphi$ (Theorem 5.13 of the source). Moreover, no algorithm computes, from a sentence that is equivalent over $\mathrm{Fin}(\sigma)$ to an existential local sentence, such an equivalent sentence (Theorem 5.15).

Over arbitrary structures, by contrast, the source proves that the sentences equivalent to existential local ones are exactly those preserved under local elementary embeddings, extending the Łoś–Tarski theorem (Theorem 1.2).

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof works over a class of finite structures that encode runs of a universal Turing machine $U$ along a successor relation $S$ together with an order (it transfers to $\mathrm{Fin}(\sigma)$ by relativising to an axiom defining that class). For a Turing machine $M$ it writes a sentence $\varphi_M \vee \varphi_{CC}$, closed under disjoint unions and computable from $M$, saying that a chain of configurations starting at the initial configuration of $U$ on the code of $M$ follows the transition relation. If $M$ halts, this sentence is equivalent to a finite disjunction of existential local sentences describing runs of bounded length; if $M$ does not halt, it has no existential local equivalent. Undecidability of halting gives the theorem.

## Sources

- Aliaume Lopez, "When locality meets preservation", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, 1–14, ACM, 2022, doi:[10.1145/3531130.3532498](https://doi.org/10.1145/3531130.3532498). Numbering of the version read, arXiv:2204.02108v1: Theorems 5.13 and 5.15 in Section 5.2 and their proofs, Theorem 1.2, Section 1.1 (existential local sentences, and closure under disjoint unions in Section 1.1.4), Lemma 2.5 and Section 3.
