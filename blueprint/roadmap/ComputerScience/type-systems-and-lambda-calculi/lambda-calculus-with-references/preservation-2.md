# Preservation for multi-step evaluation

Let $\Gamma$ be a variable context and $S$ a
store typing. If a term $t$ has type $T$ under $\Gamma$ and $S$, the store $\mu$ is well typed
under $\Gamma$ and $S$, and $t$ with store $\mu$ evaluates in zero or more steps to $t'$ with
store $\mu'$, then there is a store typing $S'$ having $S$ as a prefix such that $t'$ has type
$T$ under $\Gamma$ and $S'$ and $\mu'$ is well typed under $\Gamma$ and $S'$.
