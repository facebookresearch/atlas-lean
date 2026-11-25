# Relational interpretation of Fω types

For a [type operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$ and an environment $\rho$ assigning to each type variable $\alpha_i$
of kind $\kappa_i$ in $\Delta$ an element of $[\![\kappa_i]\!]_{\mathcal{R}}$ (a [β-invariant
relation](../../system-f/binary-beta-invariant-relations/rel.md) for kind $\star$, a function
between such interpretations for higher kinds), the relational interpretation $[\![A]\!]_\rho \in
[\![\kappa]\!]_{\mathcal{R}}$ is the
[evaluation](../semantic-kind-interpretation-and-substitution/eval.md) of $A$ in the [relational
kind algebra](relational-algebra.md).
