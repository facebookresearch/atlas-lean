# Expansive spineless extensions of FLe have undecidable theoremhood

If a finite set of spineless simple equations contains an expansive one, the variety of commutative residuated lattices it axiomatizes has an undecidable equational theory; so infinitely many extensions of $\mathsf{FL_e}$ by structural rules, such as the rule for $x \leq x^2 \vee x^3$, have undecidable theoremhood.

**Theorem (Galatos and St. John).** Let $\Gamma$ be a finite set of [spineless simple equations](simple-and-spineless-equations-over.md) containing an expansive equation. Then the variety $\mathsf{CRL} + \Gamma$ has an undecidable equational theory (Theorem 5.9). In particular, for every one-variable basic equation $[n,P] : x^n \leq \bigvee_{p \in P} x^p$ such that $P$ contains at least two distinct positive integers and every element of $P$ is greater than $n$, $\mathsf{CRL} + [n,P]$ has an undecidable equational theory (Theorem 7.17).

Equivalently, theoremhood in the extension of $\mathsf{FL_e}$ by the corresponding structural rules is undecidable; for example for $\mathsf{FL_e}$ with the rule corresponding to $x \leq x^2 \vee x^3$. Previously all known extensions of $\mathsf{FL_e}$ by structural rules had decidable theoremhood.

## Depends on

- [Simple and spineless equations over commutative residuated lattices](simple-and-spineless-equations-over.md)

## Proof depends on

- [Commutative residuated lattices with spineless equations have undecidable word problem](spineless-extensions-of-crl-have-undecidable.md)

## Expansion

An expansive equation makes $\mathsf{CRL} + \Gamma$ negatively $n$-potent for some $n$, and in commutative, negatively $n$-potent residuated lattices congruences are characterized well enough for a form of the deduction theorem: a quasiequation can be converted into an equation equivalent to it over the variety. Hence deciding the equational theory is at least as hard as acceptance of an and-branching counter machine (Corollary 5.8), and the word-problem encoding of the spineless case yields undecidability.

## Sources

- Nikolaos Galatos and Gavin St. John, "Most simple extensions of $\mathsf{FL_e}$ are undecidable", *The Journal of Symbolic Logic* 87(3):1156–1200, 2022, doi:10.1017/jsl.2021.46; read as arXiv:2005.00645v1, <https://arxiv.org/abs/2005.00645v1>: Theorem 5.9, Corollary 5.8, Lemma 5.6, Theorem 7.17 and Section 5.3 of arXiv:2005.00645v1.
