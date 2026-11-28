# Relations between NBI, LBI and multiplicative linear logic

This node covers the remaining proof-theoretic correspondences around the BI calculi: the equivalence of the natural deduction system NBI and the sequent calculus LBI, normalization of NBI, and conservativity of BI over multiplicative intuitionistic linear logic.

O'Hearn and Pym state that NBI is strongly normalizing with respect to the evident reductions and commuting conversions and has the subject reduction property (their Proposition 2), and that BI is conservative over multiplicative intuitionistic linear logic MILL: for formulas built from the multiplicative connectives only, $\varphi_1 , \dots , \varphi_n \vdash \varphi$ is provable in BI if and only if $\varphi_1^\ast, \dots, \varphi_n^\ast \vdash \varphi^\ast$ is provable in MILL, where $(-)^\ast$ replaces $\ast$ by $\otimes$ and $\mathrel{-\!\!\ast}$ by $\multimap$ (their Proposition 3(2)). They refer to Pym's sequent presentation for the connection between NBI and LBI; Galatos, Jipsen, Knudstorp and Ramanayake describe the sequent calculus and the algebraic semantics as equivalent definitions of BI. Pym's monograph, where the sequent presentation is worked out, is described by its author as of historical interest, so a page for the equivalence needs a current source.

## Depends on

- [Natural deduction for BI](natural-deduction-for-bi.md)
- [The sequent calculus LBI](sequent-calculus-lbi.md)

## Proof depends on

None.

## Expansion

This node is still to expand. A good expansion states, each on its own page and with a current source, that NBI and LBI derive the same sequents, strong normalization of NBI, and conservativity over MILL with a page for that calculus.

## Sources

- P. W. O'Hearn and D. J. Pym, "The logic of bunched implications", *The Bulletin of Symbolic Logic* 5(2) (1999), 215–244, <https://doi.org/10.2307/421090>, author copy read from the first author's publication page, <http://www0.cs.ucl.ac.uk/staff/p.ohearn/papers/BI.pdf> (numbering of the author copy; no page numbers cited): Section 2 (Lemma 1 and the paragraph after it, Proposition 2 and Proposition 3(2)).
- N. Galatos, P. Jipsen, S. B. Knudstorp and R. Ramanayake, "The logic of bunched implications is undecidable", in *41st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2026)*, Leibniz International Proceedings in Informatics, Schloss Dagstuhl, 2026, article 46, <https://doi.org/10.4230/LIPIcs.LICS.2026.46>: Section 2, first paragraph.
- D. J. Pym, "Errata and remarks for *The Semantics and Proof Theory of the Logic of Bunched Implications*", dated 1 January 2022, <https://www.cantab.net/users/david.pym/BI-monograph-errata.pdf>: abstract.
