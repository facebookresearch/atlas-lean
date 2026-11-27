# Lifting an ownership map past a binder

Let $k$ be a natural number and $\Delta$ an ownership context (a finite map from endpoints $x^{r}$
to capabilities). The lifted context $\uparrow_k\Delta$ maps $(\uparrow_k x)^{r}$ to $\Delta(x^{r})$
for every endpoint $x^{r}$ in the domain of $\Delta$ and has no other entries, where $\uparrow_k$
adds one to a variable index $\ge k$ and fixes constants and smaller variables. Since $\uparrow_k$
is injective on names, no two entries are merged.
