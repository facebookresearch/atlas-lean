# Weakening runtime typing by one fresh completed entry

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $p$ a
process, $z$ an endpoint not in the domain of $\Delta$ whose name is scoped at depth $n$ and is not
a declared trigger $\mathrm{c}_s$, and $u$ a capability whose protocol has head $\mathrm{end}$. If
$\Gamma; \Delta \vdash_n p$, then $\Gamma; \Delta[z \mapsto u] \vdash_n p$.
