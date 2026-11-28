# Cut elimination for LBI

Cut elimination holds for the bunched sequent calculus LBI: every sequent $\Gamma \vdash \varphi$ that is provable in LBI with the cut rule is provable in LBI without it.

Let $\Gamma$ be a [bunch](formulas-and-bunches-of-bi.md) and $\varphi$ a BI proposition. If $\Gamma \vdash \varphi$ is derivable in [LBI](sequent-calculus-lbi.md) using all its rules, including

$$
\frac{\Delta \vdash \psi \qquad \Gamma'(\psi) \vdash \chi}{\Gamma'(\Delta) \vdash \chi}\ (\mathrm{cut}),
$$

then $\Gamma \vdash \varphi$ has a derivation in LBI with no instance of (cut). The cut formula $\psi$ may occur anywhere in the bunch $\Gamma'(\psi)$, inside either kind of combination, and the structural rules (w), (c) and ($\equiv$) remain available in the cut-free derivation. No bound on the size of the cut-free derivation is part of the statement.

## Depends on

- [Formulas and bunches of BI](formulas-and-bunches-of-bi.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

- [BI-algebras](bi-algebras.md)
- [Soundness and completeness of BI for BI-algebras](soundness-and-completeness-for-bi-algebras.md)

## Expansion

The theorem is stated by Galmiche, Méry and Pym, citing Pym's 2002 monograph. The monograph's errata (chapter 6, p. 91) record that its proof sketch for cut elimination is not adequate and that a much stronger argument is required, and point to Brotherston (2012) and Gheorghiu and Marin (2020) for proofs. Frumin explains where a naive Gentzen-style argument for LBI breaks: with explicit contraction on ";", pushing each cut upwards does not necessarily work, which leads to a multicut rule combining contraction and cut whose original treatment covered only some cases. Frumin gives a semantic proof, formalized in Coq: for the calculus of his Figure 1, which is LBI with the axiom restricted to propositional letters, he interprets sequents in a BI-algebra of sets of bunches closed under a suitable closure operator, shows that a sequent holding there has a cut-free derivation (his Theorem 6.7), and concludes that cut is admissible in the cut-free calculus (his Theorem 6.8), using soundness of the calculus in every BI-algebra (his Theorem 4.3) to interpret the premises in that algebra; the axiom $\varphi \vdash \varphi$ for every proposition is derivable without cut (his Proposition 3.1), so the result transfers to LBI as defined here. Sources that use this result to prove unprovability, such as the [incompleteness of the elementary resource semantics with $\bot$](elementary-resource-semantics-is-incomplete-with-bottom.md), rely on the subformula property of cut-free derivations, which follows because every rule other than (cut) has premises built from subformulas of its conclusion. The analogous admissibility of cut for [natural deduction NBI](natural-deduction-for-bi.md) is O'Hearn and Pym's Lemma 1.

## Sources

- D. Galmiche, D. Méry and D. Pym, "The semantics of BI and resource tableaux", *Mathematical Structures in Computer Science* 15(6) (2005), 1033–1088, <https://doi.org/10.1017/S0960129505004858>; numbering from the author copy read (received 31 March 2005), <https://www.cantab.net/users/david.pym/sem-res-tab.pdf>: Theorem 2.1 (Cut-elimination) and Figure 1.
- D. Frumin, "Semantic cut elimination for the logic of bunched implications, formalized in Coq", in *Proceedings of the 11th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2022)*, ACM, 2022, <https://doi.org/10.1145/3497775.3503690>; read as arXiv:2112.05515v1, <https://arxiv.org/abs/2112.05515v1>: Section 1 (the gap in the monograph's proof and the role of contraction), Section 3, Figure 1 and Proposition 3.1, Section 4, Theorem 4.3, and Section 6, Theorems 6.7 and 6.8.
- D. J. Pym, "Errata and remarks for *The Semantics and Proof Theory of the Logic of Bunched Implications*", dated 1 January 2022, <https://www.cantab.net/users/david.pym/BI-monograph-errata.pdf>: Chapter 6, item 2 (p. 91).
- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2, Lemma 1.
