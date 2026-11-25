# Availability of all declared services

Let $\Gamma$ be a service environment (a finite map from natural numbers to service signatures) and
$p$ a process. All services of $\Gamma$ are available in $p$ when for every $s$ declared in
$\Gamma$, $p$ offers $\mathrm{c}_s$ persistently: $p$ contains, under parallel compositions and
restrictions only, a replication $!q$ whose body $q$ has an unguarded input on $\mathrm{c}_s$ (under
parallel compositions, restrictions and replications only).
