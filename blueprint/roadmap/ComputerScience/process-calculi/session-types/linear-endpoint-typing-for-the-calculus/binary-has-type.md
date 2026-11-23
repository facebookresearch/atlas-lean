# Binary session typing embeds into polarized endpoint typing

Let $\Gamma : \mathbb{N} \to \mathcal{S}$ be a finite binary session context, $(p,q)$ a pair of
processes and $\rho : \mathbb{N} \to \mathbb{N}$ an arbitrary rank assignment. If $(p,q)$ is binary
typed in $\Gamma$ (that is, $\Gamma \vdash_0 p$ and $\overline{\Gamma} \vdash_0 q$ in the typing of
sequential threads), then there is a natural number $N$ such that

$$
\Delta^{+}_{N} \cup \Delta^{-}_{N} \vdash_0 p \mid q
$$

in endpoint typing. Here $\Delta^{+}_{N}$ is the ownership context mapping the endpoint
$\mathrm{c}_i^{+}$ to the capability $(\rho(i), \iota(\Gamma(i)))$ for every $i < N$ and having no
other entries, $\Delta^{-}_{N}$ maps $\mathrm{c}_i^{-}$ to $(\rho(i), \iota(\overline{\Gamma(i)}))$
for $i < N$, and $\iota$ translates session types into protocols by $\iota(\mathrm{end}) =
\mathrm{end}$, $\iota({!S}) = {!\mathrm{N}}.\iota(S)$ and $\iota({?S}) = {?\mathrm{N}}.\iota(S)$.
