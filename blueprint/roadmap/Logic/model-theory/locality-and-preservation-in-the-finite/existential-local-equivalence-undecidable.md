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

Both proofs work over a class $\mathcal C_{\mathrm{ord}}$ of finite structures that encode runs of a universal Turing machine $U$ along a successor relation $S$ together with an order; this transfers to $\mathrm{Fin}(\sigma)$ by relativising to an axiom defining the class (Fact 5.2 of the source). Over $\mathcal C_{\mathrm{ord}}$, the existential local sentence $\varphi_{CC}$ says that the structure has at least two connected components (Lemma 5.3), and $1$-local formulas $\theta_I(x)$, $\theta_T(x, y)$ and $\theta_F(x)$ say that the configuration at $x$ is initial on the code $\langle M\rangle$ of a Turing machine $M$, that the configuration at $y$ follows the one at $x$, and that the configuration at $x$ is final.

*Theorem 5.13.* Let $\varphi_M = \exists x\, \theta_I(x) \wedge \forall x, y\, (S(x, y) \wedge \neg(x \le y) \Rightarrow \theta_T(x, y))$, saying that the structure starts at the initial configuration of $U$ on $\langle M\rangle$ and follows its transition relation, and $\varphi = \varphi_M \vee \varphi_{CC}$, which is closed under disjoint unions and computable from $M$. If $M$ halts, the run of $U$ has bounded length and $\varphi$ is equivalent to $\varphi_{CC}$ together with a finite disjunction of existential local sentences describing runs of bounded length. If $M$ does not halt, an existential local sentence with $k$ quantifiers and radius $r$ that holds in a run longer than $k(2r+1)$ also holds after changing a configuration it does not see, so $\varphi$ has no existential local equivalent.

*Theorem 5.15.* Here $\varphi_M$ also asserts a final configuration, $\exists x\, \theta_F(x)$, and again $\varphi = \varphi_M \vee \varphi_{CC}$. If $M$ halts, $\varphi$ has an existential local equivalent as before; if $M$ does not halt, $\varphi_M$ has no model and $\varphi$ is equivalent to $\varphi_{CC}$. So $\varphi$ always has an existential local equivalent, and an algorithm computing one, with $k$ quantifiers and radius $r$, would show that $M$ halts within $2k(2r+1)$ steps if at all, which decides halting.

A good expansion links pages for the encoding of runs of $U$ in $\mathcal C_{\mathrm{ord}}$ with the formulas $\theta_I$, $\theta_T$, $\theta_F$ and $\varphi_{CC}$ (Lemma 5.9, Facts 5.10 and 5.11, and Lemma 5.3) and for the relativisation of Fact 5.2.

## Sources

- Aliaume Lopez, "When locality meets preservation", in *Proceedings of the 37th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2022)*, 1–14, ACM, 2022, doi:[10.1145/3531130.3532498](https://doi.org/10.1145/3531130.3532498). Numbering of the version read, arXiv:2204.02108v1: Theorems 5.13 and 5.15 in Section 5.2 and their proofs, with Fact 5.2, Lemmas 5.3 and 5.9 and Facts 5.10 and 5.11, Theorem 1.2, Section 1.1 (existential local sentences, and closure under disjoint unions in Section 1.1.4), Lemma 2.5 and Section 3.
