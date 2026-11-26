# Guarded frontier of guards and idle service templates

Let $\Gamma$ be a service environment. A guarded frontier for $\Gamma$ is a process built by the
following rules: every service template for $\Gamma$ (built from $\mathbf{0}$ and inputs on declared
triggers by $\mid$, $\nu$ and replication) is a guarded frontier; every output $\overline{a}\langle
b\rangle.p$ and every input $a(\cdot).p$ is a guarded frontier; and if $p$ and $q$ are guarded
frontiers, so is $p \mid q$.
