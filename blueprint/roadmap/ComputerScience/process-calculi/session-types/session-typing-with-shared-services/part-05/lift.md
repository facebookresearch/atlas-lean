# Binder lifting preserves runtime typing

Let $n$, $k$ be natural numbers, $\Gamma$ a service environment, $\Delta$ an ownership context and
$p$ a process. If $\Gamma; \Delta \vdash_n p$, then $\Gamma; \uparrow_k\Delta \vdash_{n+1}
\uparrow_k p$, where $\uparrow_k$ adds one to every variable index $\ge k$.
