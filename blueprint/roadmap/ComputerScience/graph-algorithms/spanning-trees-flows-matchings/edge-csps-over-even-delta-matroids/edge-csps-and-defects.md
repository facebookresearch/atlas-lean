# Edge CSPs, occurrence labelings and defects

An **edge CSP** is a Boolean constraint satisfaction instance in which every variable lies in the scope of exactly two distinct constraints and occurs at most once in each scope (so variables are edges between constraints of a multigraph). An **occurrence labeling** (the source's *edge labeling*) assigns a Boolean value to every variable-constraint incidence; it is **valid** if every constraint's tuple of labels lies in its relation. A variable is a **defect** of the labeling (the source calls it *inconsistent*) if its two occurrences carry different labels. A valid labeling is **optimal** if no valid labeling has fewer defects. The instance is satisfiable if and only if some valid labeling has no defects, that is, if and only if an optimal labeling has no defects. Since labels are chosen per incidence, a valid labeling exists exactly when every constraint relation is nonempty. With the relation "exactly one incident occurrence is $1$" at every vertex of a loopless graph, valid defect-free labelings are perfect matchings.

## Depends on

- [Boolean constraint languages and CSP(Γ)](../../../../TheoryOfComputation/np-completeness/boolean-constraint-satisfaction/polymorphisms-of-boolean-relations/boolean-constraint-languages.md)

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), Article 22, 2019, Definitions 3 and 20.
