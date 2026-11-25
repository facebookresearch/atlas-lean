# Erasing an owned key preserves nonaliasing

Let $\Gamma$ be a service environment, $\Delta$ an ownership context and $f$ a map from names to
names that does not alias $\Delta$ with $\Gamma$ (no endpoint name of $\Delta$ is sent by $f$ to a
declared trigger). Then for every endpoint $e$, $f$ does not alias $\Delta \setminus e$ with
$\Gamma$.
