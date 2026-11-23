# Type substitution preserves Fω typing

Let $\Gamma \vdash t : A$ in pure Fω ([typing](typing.md)), with $\Gamma$ a term context over
$\Delta$, and let $\sigma : \Delta \to \mathrm{E}$ be a [kind-preserving
substitution](../intrinsically-kinded-type-operators-for-pure-f/sub.md). Then $\Gamma[\sigma] \vdash
t[\sigma] : A[\sigma]$, where $\Gamma[\sigma](i) = \Gamma(i)[\sigma]$ and $t[\sigma]$ is the [type
substitution in terms](../scoped-pure-f-terms/ty-subst.md).
