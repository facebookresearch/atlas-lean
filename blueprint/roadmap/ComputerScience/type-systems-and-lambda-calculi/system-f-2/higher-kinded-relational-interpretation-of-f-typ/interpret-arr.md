# Relational interpretation of an Fω function type

For $A, B \in \mathrm{Ty}^{\star}_{\Delta}$, every environment $\rho$ of kinded relations for
$\Delta$ and all terms $f$, $g$ of the [untyped term
model](../../system-f/the-existing-untyped-beta-conversion-term-model/model.md): $[\![A \to
B]\!]_\rho(f, g)$ holds if and only if $[\![B]\!]_\rho(f\,x, g\,y)$ holds for all terms $x$, $y$
with $[\![A]\!]_\rho(x, y)$ ([relational interpretation](interpret.md)).
