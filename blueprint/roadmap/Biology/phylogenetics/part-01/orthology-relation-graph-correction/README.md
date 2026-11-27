# Orthology relation graph correction

Tree-free orthology predictors output a graph on the genes of a family whose edges are orthologies and non-edges paralogies. Such a graph comes from a gene tree with speciation and duplication labels exactly when it is a cograph, and from a valid history under a known species tree only under a further consistency condition. Correcting noisy predictions to the nearest satisfiable or consistent graph is hard to approximate when weighted, but admits an $n$-factor algorithm and, in the unweighted maximization form, approximation schemes.

- [Weighted cograph editing of orthology relation graphs](weighted-cograph-editing-of-orthology-relation-graphs.md)
- [Approximation schemes for maximum agreement relation editing](approximation-schemes-for-maximum-agreement-relation-editing.md)
