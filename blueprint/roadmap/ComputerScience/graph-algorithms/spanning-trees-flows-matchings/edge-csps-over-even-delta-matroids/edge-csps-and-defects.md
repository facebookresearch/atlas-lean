# Edge CSPs, occurrence labelings and defects

An **edge CSP** is a Boolean constraint satisfaction instance in which every variable occurs in exactly two constraint positions (so variables are edges between constraints). An **occurrence labeling** assigns a Boolean value to every occurrence; it is **valid** if every constraint's tuple of labels lies in its relation. A variable is a **defect** of the labeling if its two occurrences carry different labels. The instance is satisfiable if and only if some valid labeling has no defects. With the relation "exactly one incident occurrence is $1$" at every vertex of a graph, valid defect-free labelings are perfect matchings.

## Sources

- A. Kazda, V. Kolmogorov and M. Rolínek, "Even Delta-Matroids and the Complexity of Planar Boolean CSPs", ACM Transactions on Algorithms 15(2), 2019.
