# Generalization of a monotype

Given a typing context $\Gamma$ and a monotype $\tau$, the
generalization of $\tau$ with respect to $\Gamma$ is the type scheme obtained from $\tau$ by
turning each type variable $\alpha$ that is not free in $\Gamma$ into the bound variable with
index $\alpha$, while type variables free in $\Gamma$ stay free.
