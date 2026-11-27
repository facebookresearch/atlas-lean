# Satisfiability of two-variable logic with transitive closure is undecidable

Adding a transitive closure operator to two-variable first-order logic, which is decidable, makes satisfiability undecidable, even when only deterministic transitive closure is added.

**Theorem (Grädel, Otto and Rosen).** The satisfiability problem for two-variable first-order logic extended by the transitive closure operator, $\mathrm{FO}^2(\mathrm{TC})$, is undecidable, and so is the satisfiability problem for two-variable logic extended by the deterministic transitive closure operator, $\mathrm{FO}^2(\mathrm{DTC})$, which applies transitive closure only to paths without choices. Hence satisfiability of full [first-order logic with transitive closure](../../../../TheoryOfComputation/descriptive-complexity/transitive-closure-logic-and-nl/tcfo.md) $\mathrm{FO(TC)}$ is undecidable too.

Two-variable first-order logic $\mathrm{FO}^2$ itself is decidable, NEXPTIME-complete. Figueira, Figueira and Nakamura describe satisfiability of full transitive closure logic as highly undecidable, citing Corollary 6.7 of Grädel, Otto and Rosen, and show that the guarded negation fragment of transitive closure logic has decidable satisfiability.

## Depends on

- [Formulas of first-order logic with transitive closure](../../../../TheoryOfComputation/descriptive-complexity/transitive-closure-logic-and-nl/tcfo.md)
- [Two-variable logic and its counting extension](two-variable-logic-and-its-counting-extension.md)

## Proof depends on

None.

## Expansion

The copies read state the result without proof. Immerman, Rabinovich, Reps, Sagiv and Yorsh recall it as the reason that transitive closure makes even very tame logics undecidable, and note that any logic able to express tilings of a grid has undecidable satisfiability; the original proof is in Grädel, Otto and Rosen and is not reproduced here.

## Sources

- E. Grädel, M. Otto and E. Rosen, "Undecidability results on two-variable logics", *Archive for Mathematical Logic* 38(4–5):313–354, 1999, doi:10.1007/s001530050130 (original source, cited beside the copies read).
- N. Immerman, A. Rabinovich, T. Reps, M. Sagiv and G. Yorsh, "The boundary between decidability and undecidability for transitive-closure logics", in *Computer Science Logic (CSL 2004)*, Lecture Notes in Computer Science 3210, Springer, 2004, pp. 160–174, doi:10.1007/978-3-540-30124-0_15; read in the authors' open-access copy at <https://people.cs.umass.edu/~immerman/pub/eadtc.pdf>: Section 2 and Figure 1, which state that $\mathrm{FO}^2(\mathrm{TC})$ and even $\mathrm{FO}^2(\mathrm{DTC})$ are undecidable and that $\mathrm{FO}^2$ is NEXPTIME-complete.
- D. Figueira, S. Figueira and Y. Nakamura, "Guarded negation transitive closure logic", in *41st Annual ACM/IEEE Symposium on Logic in Computer Science (LICS 2026)*, Leibniz International Proceedings in Informatics 380, Schloss Dagstuhl, 2026, article 43, doi:10.4230/LIPIcs.LICS.2026.43; read as arXiv:2501.15303v4, <https://arxiv.org/abs/2501.15303v4>: Section 1, paragraph "Related work".
