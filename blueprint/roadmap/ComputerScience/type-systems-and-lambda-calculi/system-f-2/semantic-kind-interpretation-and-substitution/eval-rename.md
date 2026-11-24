# Evaluation of a renamed type operator

Let $M$ be a [kind algebra](kind-algebra.md), $\eta$ a [semantic environment](kenv.md) for
$\mathrm{E}$, $\rho : \Delta \to \mathrm{E}$ a [kind-preserving
renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md) and $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$. Then $[\![A\langle\rho\rangle]\!]_\eta = [\![A]\!]_{\eta \circ
\rho}$ ([evaluation](eval.md),
[renaming](../intrinsically-kinded-type-operators-for-pure-f/rename.md)).
