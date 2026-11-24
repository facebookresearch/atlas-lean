# The abstraction $\lambda f.\, f\, f$ has no type

For every typing context $\Gamma$,
every variable name $f$ and every monotype $\tau$, the judgment
$\Gamma \vdash \lambda f.\, f\, f : \tau$ does not hold.

The λ-bound variable $f$ is monomorphic, so it cannot be applied to itself.
