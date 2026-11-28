# Except-0 modality and timeless propositions

The *except-0 modality* is defined by $\diamond P \triangleq P \vee \triangleright \mathrm{False}$, so that $\diamond P$ is true at index 0 and agrees with $P$ above 0; a proposition is *timeless* when $\triangleright P \vdash \diamond P$.

In the Iris base logic, $\diamond P \triangleq P \vee \triangleright \mathrm{False}$ and $\mathrm{timeless}(P) \triangleq (\triangleright P \vdash \diamond P)$. Semantically, $\triangleright \mathrm{False}$ is true exactly at index 0. The source recalls that Iris 1.0 and 2.0 defined timelessness semantically (truth at index 0, at a resource valid at the index, gives truth at every index); Iris 3 uses the definition in the logic above instead, and the page does not claim the two are equivalent. The except-0 modality satisfies $P \vdash \diamond P$, $\diamond\diamond P \vdash \diamond P$ and monotonicity, and if $P \vdash \diamond Q$ and $P$ is timeless then $\triangleright P \vdash \diamond Q$.

## Depends on

- [Iris base logic](iris-base-logic.md)

## Proof depends on

- [Iris base logic](iris-base-logic.md)

## Expansion

The naive definition $\triangleright P \vdash P$ is unusable: with Löb induction it would force $P$ to be True, because $\triangleright P$ holds at index 0. The source shows that timelessness is preserved by $\wedge, \vee, \Rightarrow, \forall, \exists, \ast, \mathrel{-\!\!\ast}$ and $\square$, the cases $\Rightarrow$, $\mathrel{-\!\!\ast}$ and $\forall$ using the base-logic rule $\triangleright P \vdash \triangleright \mathrm{False} \vee (\triangleright \mathrm{False} \Rightarrow P)$, and that ownership of an element of a discrete camera is timeless. The fancy update modality builds in except-0 to strip a later from timeless hypotheses.

## Sources

- R. Jung, R. Krebbers, J.-H. Jourdan, A. Bizjak, L. Birkedal and D. Dreyer, "Iris from the ground up: a modular foundation for higher-order concurrent separation logic", *Journal of Functional Programming* 28, e20, 2018, open access <https://doi.org/10.1017/S0956796818000151> (version of record, Cambridge University Press), Section 5.7 (except-0, the definition of timelessness in the logic, its derived rules and the preservation and discreteness facts).
