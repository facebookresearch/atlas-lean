# Environment extension preserves runtime typing under separation

Let $n$ be a natural number, $\Gamma$, $\Xi$ service environments with $\Xi$ extending $\Gamma$,
$\Delta$ an ownership context separated from $\Xi$ and $p$ a process. If $\Gamma; \Delta \vdash_n
p$, then $\Xi; \Delta \vdash_n p$.
