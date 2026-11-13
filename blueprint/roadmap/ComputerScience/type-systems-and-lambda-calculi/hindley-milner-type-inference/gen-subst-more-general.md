# Renaming step of the substitution lemma

Let $\Gamma$ be a typing context, $\tau$ a
monotype and $s$ a type substitution. Write $s\Gamma$ for the context obtained by applying $s$ to
every scheme of $\Gamma$, and let $N$ be one more than the largest free type variable of
$s\Gamma$, with $N = 1$ if $s\Gamma$ has none. Let $\rho$ be the substitution sending a type
variable $y$ to $s(y)$ if $y$ is free in $\Gamma$, and to the type variable $y + N$ otherwise.
Then the generalization of $\rho(\tau)$ with respect to $s\Gamma$ is more general than the scheme
obtained by applying $s$ to the free type variables of the generalization of $\tau$ with respect
to $\Gamma$.
