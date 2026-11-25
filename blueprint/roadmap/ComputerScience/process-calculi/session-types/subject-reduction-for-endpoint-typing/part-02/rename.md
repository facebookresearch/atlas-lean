# Collision-free renaming preserves endpoint typing

Let $n$, $m$ be natural numbers, $\Delta$ an ownership context, $p$ a process and $f$ a map from
names to names that sends names scoped at depth $n$ to names scoped at depth $m$ and whose induced
map $x^{r} \mapsto f(x)^{r}$ on endpoints is injective on the domain of $\Delta$. If $\Delta
\vdash_n p$, then $f_*\Delta \vdash_m f(p)$, where $f_*\Delta$ maps $f(x)^{r}$ to $\Delta(x^{r})$
and $f(p)$ is the capture-free renaming of $p$ by $f$.
