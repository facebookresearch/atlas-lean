# Minimal solutions of abduction in separation logic

Let predicates be sets of states $(s, h)$ of a stack and a heap, and for predicates $F, G$ consider the *abduction question*: find $M$ with $F \ast M \models G$. Order solutions by the preorder $M \le M'$ iff $M' \models M \ast \mathit{true}$ (spatially smaller) and by

$$M \precsim M' \iff (M \le M' \wedge M' \not\le M) \vee (M \le M' \wedge M' \le M \wedge M \models M'),$$

a partial order. Let $\min(F)$ be the set of states $(s, h) \models F$ such that $(s, h') \models F$ for a subheap $h' \subseteq h$ implies $h' = h$; in separation logic, $\min(F) = F \wedge \neg(F \ast \neg\mathrm{emp})$. Then $F \mathrel{-\!\!\ast} G$ is a minimal solution with respect to $\le$, and the minimal solution with respect to $\precsim$ always exists and is $\min(F \mathrel{-\!\!\ast} G)$, using the [separating implication](../separating-implication-and-small-axioms/separating-implication.md).

## Depends on

- [Separating implication](../separating-implication-and-small-axioms/separating-implication.md)

## Proof depends on

- [Adjunction between separating conjunction and separating implication](../separating-implication-and-small-axioms/adjunction-between-separating-conjunction-and-implication.md)

## Sources

- C. Calcagno, D. Distefano, P. W. O'Hearn and H. Yang, "Compositional shape analysis by means of bi-abduction", *Journal of the ACM* 58(6), 2011; accepted version (May 2011) <https://www.cs.ox.ac.uk/files/4078/jacm11-biabduction-submitted.pdf>, Section 3.3, Definition 3.9, Lemmas 3.10–3.12 and Theorem 3.13, with the ordering $\precsim$ as corrected in footnote 7 there.
