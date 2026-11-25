# Runtime typing under renamings that fix and avoid shared names

Let $n$, $m$ be natural numbers, $\Gamma$ a service environment, $\Delta$ an ownership context, $p$
a process and $f$ a map from names to names such that: $f$ sends names scoped at depth $n$ to names
scoped at depth $m$; $f(\mathrm{c}_s) = \mathrm{c}_s$ for every $s$ declared in $\Gamma$; $f$ sends
no endpoint name of $\Delta$ to a declared trigger; and $x^{r} \mapsto f(x)^{r}$ is injective on the
domain of $\Delta$. If $\Gamma; \Delta \vdash_n p$ (runtime typing with shared services), then
$\Gamma; f_*\Delta \vdash_m f(p)$, where $f_*\Delta$ maps $f(x)^{r}$ to $\Delta(x^{r})$ and $f(p)$
applies $f$ to the names of $p$ capture-free (using the extension $f^{\uparrow}$ under binders).
