# Parallel guard frontier

A process is a guard frontier if it is built by the following rules: $\mathbf{0}$ is a guard
frontier; every output $\overline{a}\langle b\rangle.p$ and every input $a(\cdot).p$ is a guard
frontier (for arbitrary names and continuations); and if $p$ and $q$ are guard frontiers, so is $p
\mid q$. Thus a guard frontier is a parallel composition of $\mathbf{0}$s and prefixed processes,
with no restriction, replication or choice at top level.
