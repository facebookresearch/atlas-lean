# Lowering of an outer context past a fresh binder

Let $\Gamma$ be an ownership context none of whose endpoints has the name $\mathrm{v}_0$. The
lowered context $\downarrow\Gamma$ maps $(x\{\mathrm{c}_0/0\})^{r}$ to $\Gamma(x^{r})$ for every
endpoint $x^{r}$ in the domain of $\Gamma$; since no such $x$ is $\mathrm{v}_0$, this lowers every
variable index of an endpoint name by one and fixes constants.
