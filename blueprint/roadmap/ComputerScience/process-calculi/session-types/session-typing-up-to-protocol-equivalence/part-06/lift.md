# Binder lifting preserves conversion ranked typing

Let $n$, $k$ be natural numbers, $\Delta$ an ownership context and $p$ a process. If $\Delta
\vdash^{\mathrm{rk}\simeq}_n p$, then $\uparrow_k\Delta \vdash^{\mathrm{rk}\simeq}_{n+1} \uparrow_k
p$, where $\uparrow_k$ adds one to every variable index $\ge k$.
