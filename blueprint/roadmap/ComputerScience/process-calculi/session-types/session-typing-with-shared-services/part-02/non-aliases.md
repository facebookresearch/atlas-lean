# Nonaliasing of owned-name images with shared constants

Let $\Gamma$ be a service environment, $\Delta$ an ownership context and $f$ a map from names to
names. The map $f$ does not alias $\Delta$ with $\Gamma$ when for every endpoint $e$ in the domain
of $\Delta$ and every $s$ declared in $\Gamma$, $f$ applied to the name of $e$ is not
$\mathrm{c}_s$.
