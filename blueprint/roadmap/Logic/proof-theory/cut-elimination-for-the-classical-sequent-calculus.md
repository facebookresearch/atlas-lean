# Cut elimination for the classical sequent calculus LK

Let LK be Gentzen's sequent calculus for classical first-order logic, with initial sequents $A \to A$ for atomic $A$, the structural rules (weakening, contraction, exchange and cut), the propositional rules and the quantifier rules, where the eigenvariable of a $\forall$-right or $\exists$-left inference does not occur in the lower sequent. If a sequent has an LK-proof $P$ all of whose cut formulas have depth at most $d$, then it has a cut-free LK-proof $P^\ast$, and the number of strong inferences satisfies $\|P^\ast\| < 2^{\|P\|}_{2d+2}$, a tower of exponentials of height $2d+2$ with $\|P\|$ on top. In particular every LK-provable sequent has a cut-free LK-proof, and, by the completeness of cut-free LK, every valid sequent of a language without equality has one.

## Expansion

This page becomes ready once these prerequisites are stated:

- The first-order sequent calculus LK: its sequents, rules and derivations, with the eigenvariable condition (statement prerequisite)
- The depth of a cut formula and the number of strong inferences of an LK-proof (statement prerequisite)
- Completeness of cut-free LK for valid sequents of a language without equality (proof prerequisite)

## Sources

- S. R. Buss, "An introduction to proof theory", in S. R. Buss (ed.), *Handbook of Proof Theory*, Elsevier, 1998, Chapter I, Section 2.3.2 (the calculus LK), Section 2.3.7 (cut-free completeness) and Section 2.4.2 (the cut-elimination theorem with its bound), <https://www.math.ucsd.edu/~sbuss/ResearchWeb/handbookI/ChapterI.pdf>
- G. Gentzen, "Untersuchungen über das logische Schließen", *Mathematische Zeitschrift* 39:176–210 and 405–431, 1935
