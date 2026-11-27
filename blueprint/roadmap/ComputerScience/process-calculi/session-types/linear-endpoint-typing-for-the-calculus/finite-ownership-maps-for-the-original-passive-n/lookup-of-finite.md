# Lookup in the finite-context ownership map

Let $\Gamma$ be a finite binary session context, $N$ a natural number, $r$ a polarity, $\rho$ a rank
assignment and $e$ an endpoint. If $e = \mathrm{c}_i^{r'}$ with $r' = r$ and $i < N$, then
$\Gamma^{r}_{N,\rho}$ maps $e$ to $(\rho(i), \iota(\Gamma(i)))$; for every other endpoint (a
constant with the other polarity or index $\ge N$, or any variable name) it has no entry. Here
$\iota$ translates ${!S}$, ${?S}$, $\mathrm{end}$ into ${!\mathrm{N}}.\iota(S)$,
${?\mathrm{N}}.\iota(S)$, $\mathrm{end}$.
