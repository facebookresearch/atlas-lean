# Bilinear Diffie–Hellman win experiment

Let $B$ be a [bilinear group interface](bilinear-group-data.md) of order $q > 1$, with source groups $G_1$, $G_2$, target group $G_T$, exponent isomorphisms $\phi_1$, $\phi_2$, $\phi_T$ from $\mathbb{Z}/q\mathbb{Z}$ and pairing $e : G_1 \times G_2 \to G_T$. Write $g_1 = \phi_1(1)$, $g_2 = \phi_2(1)$ and $g_T = \phi_T(1)$ for the generators. Let $A$ be a randomized adversary that, given $X, Y \in G_1$ and $Z \in G_2$, outputs a probability distribution $A(X, Y, Z)$ on $G_T$. For fixed $a, b, c \in \mathbb{Z}/q\mathbb{Z}$, the bilinear Diffie–Hellman win experiment runs $A$ on

$$\bigl(\phi_1(a), \phi_1(b), \phi_2(c)\bigr) = \bigl(g_1^a, g_1^b, g_2^c\bigr)$$

and outputs $\mathrm{true}$ exactly when the output of $A$ equals $\phi_T(abc) = g_T^{abc}$; it is the distribution of this indicator under the coins of $A$.
