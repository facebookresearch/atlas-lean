# Polarized ownership map of a finite channel context

Let $\Gamma : \mathbb{N} \to \mathcal{S}$ be a finite binary session context, $N$ a natural number,
$r$ a polarity and $\rho : \mathbb{N} \to \mathbb{N}$ a rank assignment. The ownership context
$\Gamma^{r}_{N,\rho}$ has domain $\{\mathrm{c}_i^{r} : i < N\}$ and maps $\mathrm{c}_i^{r}$ to the
capability $(\rho(i), \iota(\Gamma(i)))$, where $\mathrm{c}_i$ is the free channel constant numbered
$i$ and $\iota$ translates session types into protocols: $\iota(\mathrm{end}) = \mathrm{end}$,
$\iota({!S}) = {!\mathrm{N}}.\iota(S)$, $\iota({?S}) = {?\mathrm{N}}.\iota(S)$.
