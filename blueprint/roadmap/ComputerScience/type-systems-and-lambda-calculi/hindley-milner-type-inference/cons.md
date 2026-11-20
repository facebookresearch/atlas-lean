# Extending more general contexts by a binding

Let $\Gamma'$ and $\Gamma$ be typing
contexts such that $\Gamma'$ is more general than $\Gamma$, let $x$ be a name, and let $\sigma'$
and $\sigma$ be type schemes such that $\sigma'$ is more general than $\sigma$. Then the context
obtained by putting the binding $x : \sigma'$ in front of $\Gamma'$ is more general than the
context obtained by putting the binding $x : \sigma$ in front of $\Gamma$.
