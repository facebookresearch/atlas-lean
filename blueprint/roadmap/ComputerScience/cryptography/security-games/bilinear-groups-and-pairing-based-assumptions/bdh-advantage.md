# Bilinear Diffie–Hellman advantage

Let $B$ be a [bilinear group interface](bilinear-group-data.md) of order $q > 1$, with source groups $G_1$, $G_2$, target group $G_T$, exponent isomorphisms $\phi_1$, $\phi_2$, $\phi_T$ from $\mathbb{Z}/q\mathbb{Z}$ and pairing $e : G_1 \times G_2 \to G_T$. The bilinear Diffie–Hellman advantage of a randomized adversary $A$ is the [winning probability](../games-and-advantages/win-prob.md) of the [bilinear Diffie–Hellman game](bdh-game.md) against $A$: the probability that the game outputs $\mathrm{true}$.
