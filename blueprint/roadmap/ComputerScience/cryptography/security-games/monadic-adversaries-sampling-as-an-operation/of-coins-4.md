# Coin MAC forger as a monadic forger

Let $A$ be a coin MAC forger: a coin distribution $\mu$ on $R$ and, for each $r \in R$, a computation $A_r$ over the tagging oracle returning $(m, t)$. Its monadic form uses the one-operation [sampling family](coin-fam.md) drawing from $\mu$: draw $r$ from $\mu$ once, then run the [embedding](embed.md) of $A_r$.
