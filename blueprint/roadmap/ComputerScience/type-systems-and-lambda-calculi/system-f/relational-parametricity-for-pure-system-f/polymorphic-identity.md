# Closed inhabitants of the polymorphic identity type are identities

Let $t \in \mathrm{Tm}_{0,0}$ be a closed term of the [polymorphic identity type](poly-id-type.md) in the empty context. For every type $A \in \mathrm{Ty}_0$ and every term $x$ of the [untyped term model](../the-existing-untyped-beta-conversion-term-model/model.md), the application of the [erasure](../system-f-erasure-and-closing-environments/erase-model.md) of $t\,[A]$ to $x$ is [β-equivalent](../the-existing-untyped-beta-conversion-term-model/beta-eq.md) to $x$.

The conclusion is full β-conversion of erased terms, for an arbitrary locally closed input; it makes no claim about termination of call-by-value evaluation. It specializes Wadler's method of free theorems (1989, Figure 1) to this syntactic model and applies to every typed inhabitant.

## Sources

- P. Wadler, *Theorems for free!*, Proceedings of the Fourth International Conference on Functional Programming Languages and Computer Architecture (FPCA '89), ACM, 1989, 347–359.
