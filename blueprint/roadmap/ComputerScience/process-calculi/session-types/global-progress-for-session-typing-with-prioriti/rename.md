# Collision-free renaming preserves ranked typing

Let $n$, $m$ be natural numbers, $\Delta$ an ownership context, $p$ a process and $f$ a map from
names to names such that $f(a)$ is scoped at depth $m$ whenever $a$ is scoped at depth $n$, and such
that the induced map $x^{r} \mapsto f(x)^{r}$ on endpoints is injective on the domain of $\Delta$.
If $\Delta \vdash^{\mathrm{rk}}_n p$, then $f_*\Delta \vdash^{\mathrm{rk}}_m f(p)$, where
$f_*\Delta$ maps $f(x)^{r}$ to $\Delta(x^{r})$, and $f(p)$ applies $f$ to the names of $p$
capture-free: under a binder the bound variable $\mathrm{v}_0$ is fixed, and a constant
$\mathrm{c}_a$ or a variable $\mathrm{v}_{i+1}$ is sent to the image under $f$ of $\mathrm{c}_a$,
respectively $\mathrm{v}_i$, with its variable indices raised by one.
