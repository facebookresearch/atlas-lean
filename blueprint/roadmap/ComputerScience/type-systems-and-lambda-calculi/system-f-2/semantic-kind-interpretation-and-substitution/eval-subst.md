# Evaluation of a substituted type operator

Let $M$ be a [kind algebra](kind-algebra.md), $\eta$ a [semantic environment](kenv.md) for
$\mathrm{E}$, $\sigma : \Delta \to \mathrm{E}$ a [kind-preserving
substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md) and $A \in
\mathrm{Ty}^{\kappa}_{\Delta}$. Then $[\![A[\sigma]]\!]_\eta = [\![A]\!]_{\eta'}$, where
$\eta'(\alpha_i) = [\![\sigma(\alpha_i)]\!]_\eta$ ([evaluation](eval.md),
[substitution](../intrinsically-kinded-type-operators-for-pure-f/subst.md)). This holds at every
kind, including higher kinds.
