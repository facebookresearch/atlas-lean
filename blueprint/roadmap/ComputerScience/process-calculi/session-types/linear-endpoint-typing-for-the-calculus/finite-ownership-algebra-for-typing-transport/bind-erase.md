# Restriction binding commutes with erasing an owned outer key

Let $\Delta$ be an ownership context, $x^{r}$ an endpoint in the domain of $\Delta$ and $c$ a
capability. Then

$$
(\nu_c\Delta) \setminus (\uparrow_0 x)^{r} = \nu_c(\Delta \setminus x^{r}),
$$

where $\uparrow_0$ adds one to every variable index, $\nu_c\Theta$ is $\uparrow_0\Theta$ (every
variable name index of an endpoint raised by one) extended by $\mathrm{v}_0^{+} \mapsto c$ and
$\mathrm{v}_0^{-} \mapsto \bar c$, and $\Theta \setminus e$ removes the entry of $e$.
