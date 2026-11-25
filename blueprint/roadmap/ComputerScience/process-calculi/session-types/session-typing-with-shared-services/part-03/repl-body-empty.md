# Typed replication has a body with empty ownership

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process. If $\Gamma; \Delta \vdash_n {!p}$, then $p$ is a service template for $\Gamma$ (built from
$\mathbf{0}$ and inputs on declared triggers by $\mid$, $\nu$ and replication) and $\Gamma;
\emptyset \vdash_n p$.
