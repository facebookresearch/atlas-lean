# Coin signature forger as a monadic forger

Let $A$ be a coin signature forger: a coin distribution $\mu$ on $R$ and, for each public key $pk$ and $r \in R$, a computation $A_{pk, r}$ over the signing oracle returning $(m, \sigma)$. Its monadic form uses the one-operation [sampling family](coin-fam.md) drawing from $\mu$: on public key $pk$, draw $r$ from $\mu$ once, then run the [embedding](embed.md) of $A_{pk, r}$.
