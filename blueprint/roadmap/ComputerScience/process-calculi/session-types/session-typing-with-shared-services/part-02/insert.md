# Inserting a nonshared key preserves separation

Let $\Gamma$ be a service environment, $\Delta$ an ownership context separated from $\Gamma$, $e$ an
endpoint whose name is not $\mathrm{c}_s$ for any $s$ declared in $\Gamma$, and $c$ a capability.
Then $\Delta[e \mapsto c]$ is separated from $\Gamma$.
