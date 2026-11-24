# Declared signature offers survive finite reduction

Let $\Gamma$ be a service environment, $s$ a natural number, $\sigma$ a service signature and $p$,
$q$ processes such that $q$ is reachable from $p$ by finitely many (possibly zero) reduction steps.
If $\Gamma(s) = \sigma$ and $p$ offers $\mathrm{c}_s$ persistently (it contains, under parallel
compositions and restrictions only, a replication whose body has an unguarded input on
$\mathrm{c}_s$), then $q$ offers $\mathrm{c}_s$ persistently as well.
