# Idle processes have no unguarded output

Let $\Gamma$ be a service environment and $p$ an idle process for $\Gamma$: $p$ is built from
$\mathbf{0}$ and inputs $\mathrm{c}_s(\cdot).q$ on constants $s$ declared in $\Gamma$ (with
arbitrary continuations $q$) by parallel composition, restriction and replication. Then $p$ has no
unguarded output, i.e. no output prefix occurring under parallel compositions, restrictions,
replications and choices only.
