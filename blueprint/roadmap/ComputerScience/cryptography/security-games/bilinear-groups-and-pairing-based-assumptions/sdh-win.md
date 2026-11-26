# q-SDH win experiment

Let $B$ be a [bilinear group interface](bilinear-group-data.md) of order $q > 1$, with source groups $G_1$, $G_2$, target group $G_T$, exponent isomorphisms $\phi_1$, $\phi_2$, $\phi_T$ from $\mathbb{Z}/q\mathbb{Z}$ and pairing $e : G_1 \times G_2 \to G_T$. Write $g_1 = \phi_1(1)$, $g_2 = \phi_2(1)$ and $g_T = \phi_T(1)$ for the generators. Let $t$ be a natural number, the degree parameter of the q-SDH problem (written $t$ because $q$ is the group order). A q-SDH adversary $A$ takes a tuple $(X_0, \dots, X_t)$ of elements of $G_1$ and two elements of $G_2$, and outputs a probability distribution on pairs $(c, h) \in \mathbb{Z}/q\mathbb{Z} \times G_1$. For a fixed secret $x \in \mathbb{Z}/q\mathbb{Z}$, the q-SDH win experiment runs $A$ on

$$\bigl(\phi_1(x^0), \phi_1(x^1), \dots, \phi_1(x^t)\bigr), \quad g_2, \quad \phi_2(x),$$

that is, on $(g_1, g_1^x, \dots, g_1^{x^t})$, $g_2$ and $g_2^x$, and outputs $\mathrm{true}$ exactly when its output $(c, h)$ passes the pairing check

$$e\bigl(h, \phi_2(x + c)\bigr) = e(g_1, g_2).$$

Writing $h = \phi_1(a)$, the check says $a(x + c) = 1$ in $\mathbb{Z}/q\mathbb{Z}$. So it fails whenever $x + c$ is not a unit, and when $x + c$ is a unit it holds exactly when $h = \phi_1\bigl((x + c)^{-1}\bigr)$ ([check at a unit denominator](sdh-check-iff.md)); at prime order this is the success event of Boneh and Boyen, $c \ne -x$ and $h = g_1^{1/(x + c)}$ ([check at prime order](sdh-check-iff-prime.md)).

## Sources

- D. Boneh and X. Boyen, *Short Signatures Without Random Oracles and the SDH Assumption in Bilinear Groups*, J. Cryptology 21 (2008), §3.1.
