# q-SDH check at a unit denominator

Let $B$ be a [bilinear group interface](bilinear-group-data.md) of order $q > 1$, with source groups $G_1$, $G_2$, target group $G_T$, exponent isomorphisms $\phi_1$, $\phi_2$, $\phi_T$ from $\mathbb{Z}/q\mathbb{Z}$ and pairing $e : G_1 \times G_2 \to G_T$. Write $g_1 = \phi_1(1)$, $g_2 = \phi_2(1)$ and $g_T = \phi_T(1)$ for the generators. Let $x, c \in \mathbb{Z}/q\mathbb{Z}$ with $x + c$ a unit, and let $h \in G_1$. Then

$$e\bigl(h, \phi_2(x + c)\bigr) = e(g_1, g_2) \iff h = \phi_1\bigl((x + c)^{-1}\bigr).$$
