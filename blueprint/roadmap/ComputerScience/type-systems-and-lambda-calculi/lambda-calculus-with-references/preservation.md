# Preservation for the lambda calculus with references

Let $\Gamma$ be a variable context
and $S$ a store typing. If a term $t$ has type $T$ under $\Gamma$ and $S$, the store $\mu$ is
well typed under $\Gamma$ and $S$, and $t$ with store $\mu$ takes one evaluation step to $t'$
with store $\mu'$, then there is a store typing $S'$ having $S$ as a prefix such that $t'$ has
type $T$ under $\Gamma$ and $S'$ and $\mu'$ is well typed under $\Gamma$ and $S'$.

This is TAPL Theorem 13.5.3, with the extension of store typings taken as the prefix order on
lists.
