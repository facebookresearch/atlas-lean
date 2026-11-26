# Finite ownership map commutes with channel advancement

Let $\Gamma$ be a finite binary session context, $a < N$ natural numbers, $S$ a session type, $r$ a
polarity and $\rho$ a rank assignment. Then

$$
(\Gamma[a \mapsto S])^{r}_{N,\rho} = \Gamma^{r}_{N,\rho}[\mathrm{c}_a^{r} \mapsto (\rho(a), \iota(S))],
$$

where $\Gamma[a \mapsto S]$ replaces the entry of $\Gamma$ at $a$ by $S$, $\Gamma^{r}_{N,\rho}$ maps
$\mathrm{c}_i^{r}$ to $(\rho(i), \iota(\Gamma(i)))$ for $i < N$, and $\iota$ translates session
types into protocols with passive name payloads.
