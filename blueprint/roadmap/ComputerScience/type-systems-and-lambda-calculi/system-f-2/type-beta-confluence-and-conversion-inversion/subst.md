# Parallel type-beta reduction is stable under substitution

Let $A \Rrightarrow B$ for $A, B \in \mathrm{Ty}^{\kappa}_{\Delta}$ ([parallel type
β-reduction](par.md)) and let $\sigma, \tau : \Delta \to \mathrm{E}$ be [kind-preserving
substitutions](../intrinsically-kinded-type-operators-for-pure-f/sub.md) with $\sigma(\alpha_i)
\Rrightarrow \tau(\alpha_i)$ for every type variable $\alpha_i$ of $\Delta$. Then $A[\sigma]
\Rrightarrow B[\tau]$.
