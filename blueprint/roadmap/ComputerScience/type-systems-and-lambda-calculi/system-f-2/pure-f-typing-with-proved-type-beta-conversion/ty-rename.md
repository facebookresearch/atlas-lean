# Type renaming preserves Fω typing

Let $\Gamma \vdash t : A$ in pure Fω ([typing](typing.md)), with $\Gamma$ a term context over
$\Delta$, and let $\rho : \Delta \to \mathrm{E}$ be a [kind-preserving
renaming](../intrinsically-kinded-type-operators-for-pure-f/kren.md). Then $\Gamma\langle\rho\rangle
\vdash t\langle\rho\rangle : A\langle\rho\rangle$, where $\Gamma\langle\rho\rangle(i) =
\Gamma(i)\langle\rho\rangle$ and $t\langle\rho\rangle$ is the [type renaming in
terms](../scoped-pure-f-terms/ty-rename.md).
