# Renaming the free variables of a normal form

Let $\rho$ be a renaming from a context $\Gamma$ to a context $\Delta$. A normal form of type $A$
in $\Gamma$ is renamed to a normal form of type $A$ in $\Delta$ by recursion, simultaneously with
the [renaming of neutral terms](rename-5.md): a neutral normal form is renamed as a neutral term,
and $\lambda t$ becomes $\lambda t'$, where $t'$ is $t$ renamed along the lift of $\rho$ to the
extended contexts, which fixes the new variable and acts as $\rho$ on the others.
