# Renaming the free variables of a neutral term

Let $\rho$ be a renaming from a context $\Gamma$ to a context $\Delta$, which sends every
variable of type $A$ in $\Gamma$ to a variable of type $A$ in $\Delta$. A neutral term of type
$A$ in $\Gamma$ is renamed to a neutral term of type $A$ in $\Delta$ by recursion, simultaneously
with the [renaming of normal forms](rename-6.md): a variable $x$ becomes $\rho(x)$, and an
application $f\,a$ becomes the renamed $f$ applied to the renamed normal form $a$.
