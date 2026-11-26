# Decisional Diffie–Hellman advantage in the first source group

Let $B$ be a [bilinear group interface](bilinear-group-data.md) of order $q > 1$, with source groups $G_1$, $G_2$, target group $G_T$, exponent isomorphisms $\phi_1$, $\phi_2$, $\phi_T$ from $\mathbb{Z}/q\mathbb{Z}$ and pairing $e : G_1 \times G_2 \to G_T$. The decisional Diffie–Hellman advantage in $G_1$ of a randomized distinguisher $D$ is the [distinguishing advantage](../games-and-advantages/advantage.md) between the [real game](ddh1-real-game.md) and the [random game](ddh1-random-game.md):

$$\bigl|\Pr[\text{real game outputs } \mathrm{true}] - \Pr[\text{random game outputs } \mathrm{true}]\bigr|.$$
