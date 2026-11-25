# Updating an already-owned key preserves nonaliasing

Let $\Gamma$ be a service environment, $\Delta$ an ownership context, $f$ a map from names to names
that does not alias $\Delta$ with $\Gamma$, $e$ an endpoint in the domain of $\Delta$ and $c$ a
capability. Then $f$ does not alias $\Delta[e \mapsto c]$ with $\Gamma$.
