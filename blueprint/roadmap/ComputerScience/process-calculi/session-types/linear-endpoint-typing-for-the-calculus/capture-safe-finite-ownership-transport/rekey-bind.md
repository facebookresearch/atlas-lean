# Rekeying commutes with binding a private pair

Let $f$ be a map from names to names, $\Delta$ an ownership context and $c$ a capability, such that
$x^{r} \mapsto f(x)^{r}$ is injective on the domain of $\Delta$ and $x^{r} \mapsto
f^{\uparrow}(x)^{r}$ is injective on the domain of $\nu_c\Delta$. Then $f^{\uparrow}_*(\nu_c\Delta)
= \nu_c(f_*\Delta)$, where $g_*\Theta$ maps $g(x)^{r}$ to $\Theta(x^{r})$, $\nu_c\Theta$ is
$\uparrow_0\Theta$ extended by $\mathrm{v}_0^{+} \mapsto c$ and $\mathrm{v}_0^{-} \mapsto \bar c$,
and $f^{\uparrow}$ fixes $\mathrm{v}_0$ and sends $\mathrm{v}_{i+1}$, $\mathrm{c}_a$ to $\uparrow_0
f(\mathrm{v}_i)$, $\uparrow_0 f(\mathrm{c}_a)$.
