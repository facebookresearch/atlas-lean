# Owned names absent from a runtime process are completed

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context and $p$ a
process with $\Gamma; \Delta \vdash_n p$. Let $z$ be an endpoint whose name does not occur in $p$
(in no subject or payload position, the tracked index being raised under each binder) and $t$ a
capability with $\Delta(z) = t$. Then the protocol of $t$ has head $\mathrm{end}$.
