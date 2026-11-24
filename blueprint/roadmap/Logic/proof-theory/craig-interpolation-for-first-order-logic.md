# Craig interpolation for first-order logic

Work in first-order logic without equality, extended with the logical constants $\top$ and $\bot$, and for a formula or list of formulas $X$ let $L(X)$ be the set of constant, function and predicate symbols and free variables occurring in $X$. If $A \to B$ is valid, there is a formula $C$ with $L(C) \subseteq L(A) \cap L(B)$ such that $A \to C$ and $C \to B$ are both valid. More generally, if the sequent $\Gamma_1, \Gamma_2 \to \Delta_1, \Delta_2$ is valid, there is a formula $C$ with $L(C) \subseteq L(\Gamma_1, \Delta_1) \cap L(\Gamma_2, \Delta_2)$ such that $\Gamma_1 \to \Delta_1, C$ and $C, \Gamma_2 \to \Delta_2$ are both valid; the interpolant is obtained by induction on a cut-free LK-proof.

## Proof depends on

- [Cut elimination for the classical sequent calculus LK](cut-elimination-for-the-classical-sequent-calculus.md)

## Sources

- S. R. Buss, "An introduction to proof theory", in S. R. Buss (ed.), *Handbook of Proof Theory*, Elsevier, 1998, Chapter I, Section 2.5.5, Craig's interpolation theorem, <https://www.math.ucsd.edu/~sbuss/ResearchWeb/handbookI/ChapterI.pdf>
- W. Craig, "Three uses of the Herbrand-Gentzen theorem in relating model theory and proof theory", *Journal of Symbolic Logic* 22(3):269–285, 1957
