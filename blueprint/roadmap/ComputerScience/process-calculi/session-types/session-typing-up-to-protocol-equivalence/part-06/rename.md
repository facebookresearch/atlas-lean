# Collision-free renaming preserves conversion ranked typing

Let $n$, $m$ be natural numbers, $\Delta$ an ownership context, $p$ a process and $f$ a map from
names to names that sends names scoped at depth $n$ to names scoped at depth $m$ and whose induced
map $x^{r} \mapsto f(x)^{r}$ on endpoints is injective on the domain of $\Delta$. If $\Delta
\vdash^{\mathrm{rk}\simeq}_n p$, then $f_*\Delta \vdash^{\mathrm{rk}\simeq}_m f(p)$, where
$f_*\Delta$ maps $f(x)^{r}$ to $\Delta(x^{r})$ and $f(p)$ applies $f$ to the names of $p$
capture-free (under a binder $\mathrm{v}_0$ is fixed and $\mathrm{c}_a$, $\mathrm{v}_{i+1}$ are sent
to $\uparrow_0 f(\mathrm{c}_a)$, $\uparrow_0 f(\mathrm{v}_i)$).
