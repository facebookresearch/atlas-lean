# Type-beta conversion is stable under renaming

Let $A, B \in \mathrm{Ty}^{\kappa}_{\Delta}$ with $A \equiv_\beta B$ ([type β-conversion](conv.md))
and $\rho : \Delta \to \mathrm{E}$ a [kind-preserving
renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md). Then $A\langle\rho\rangle
\equiv_\beta B\langle\rho\rangle$
([renaming](../intrinsically-kinded-type-operators-for-pure-f/rename.md)).
