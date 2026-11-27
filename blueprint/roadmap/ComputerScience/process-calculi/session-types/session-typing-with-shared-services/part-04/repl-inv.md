# Inversion of runtime typing for replication

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process with $\Gamma; \Delta \vdash_n {!p}$ (runtime typing with shared services). Then every
capability of $\Delta$ has head $\mathrm{end}$, every endpoint of $\Delta$ has a name scoped at
depth $n$, $\Delta$ is separated from $\Gamma$, $p$ is a service template for $\Gamma$ (built from
$\mathbf{0}$ and inputs on declared triggers by $\mid$, $\nu$ and replication), and $\Gamma;
\emptyset \vdash_n p$.
