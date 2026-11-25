# Injectivity of rekeying under a restriction binding

Let $f$ be a map from names to names, $\Delta$ an ownership context such that $x^{r} \mapsto
f(x)^{r}$ is injective on the domain of $\Delta$, and $c$ a capability. Then $x^{r} \mapsto
f^{\uparrow}(x)^{r}$ is injective on the domain of $\nu_c\Delta$, the context $\uparrow_0\Delta$
extended by $\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$; here $f^{\uparrow}$
fixes $\mathrm{v}_0$ and sends $\mathrm{v}_{i+1}$, $\mathrm{c}_a$ to $\uparrow_0 f(\mathrm{v}_i)$,
$\uparrow_0 f(\mathrm{c}_a)$.
