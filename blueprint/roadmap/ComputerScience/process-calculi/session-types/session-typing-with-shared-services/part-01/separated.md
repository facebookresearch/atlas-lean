# Separation of owned linear names from shared names

A service environment $\Gamma$ and an ownership context $\Delta$ are separated when no endpoint
owned by $\Delta$ has the trigger of a declared service as its name: for every endpoint $e$ with
$\Delta(e)$ defined and every $s$ declared in $\Gamma$, the name of $e$ is not $\mathrm{c}_s$.
