# Injectivity of rekeying after receiving a fresh role

Let $f$ be a map from names to names, $\Delta$ an ownership context such that $x^{r} \mapsto
f(x)^{r}$ is injective on the domain of $\Delta$, $r$ a polarity and $c$ a capability. Then $x^{r'}
\mapsto f^{\uparrow}(x)^{r'}$ is injective on the domain of $(\uparrow_0\Delta)[\mathrm{v}_0^{r}
\mapsto c]$; here $f^{\uparrow}$ fixes $\mathrm{v}_0$ and sends $\mathrm{v}_{i+1}$, $\mathrm{c}_a$
to $\uparrow_0 f(\mathrm{v}_i)$, $\uparrow_0 f(\mathrm{c}_a)$.
