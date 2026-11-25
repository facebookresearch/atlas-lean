# Evaluation of an instantiated type operator

Let $M$ be a [kind algebra](kind-algebra.md), $\eta$ a [semantic environment](kenv.md) for $\Delta$,
$B \in \mathrm{Ty}^{\kappa}_{\mu \cdot \Delta}$ and $A \in \mathrm{Ty}^{\mu}_{\Delta}$. Then
$[\![B[A]]\!]_\eta = [\![B]\!]_{[\![A]\!]_\eta \cdot \eta}$ ([evaluation](eval.md),
[instantiation](../intrinsically-kinded-type-operators-for-pure-f/instantiate.md),
[extension](extend.md)).
