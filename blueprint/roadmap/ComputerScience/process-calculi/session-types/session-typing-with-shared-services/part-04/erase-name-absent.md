# Erasing a key whose name is absent preserves runtime typing

Let $n$ be a natural number, $\Gamma$ a service environment, $\Delta$ an ownership context, $p$ a
process and $z$ an endpoint whose name does not occur in $p$. If $\Gamma; \Delta \vdash_n p$, then
$\Gamma; \Delta \setminus z \vdash_n p$.
