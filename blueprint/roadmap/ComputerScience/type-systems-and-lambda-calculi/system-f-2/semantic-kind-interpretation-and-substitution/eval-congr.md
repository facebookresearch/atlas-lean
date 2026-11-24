# Evaluation depends only on the environment pointwise

Let $M$ be a [kind algebra](kind-algebra.md) on a set $X$ and $\eta$, $\eta'$ [semantic
environments](kenv.md) for $\Delta$ with $\eta(\alpha_i) = \eta'(\alpha_i)$ for every type variable
$\alpha_i$ of $\Delta$. Then $[\![A]\!]_\eta = [\![A]\!]_{\eta'}$ for every [type
operator](../intrinsically-kinded-type-operators-for-pure-f/ty.md) $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$ ([evaluation](eval.md)).
