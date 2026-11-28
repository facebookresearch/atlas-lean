# q-SDH game

Let $B$ be a [bilinear group interface](bilinear-group-data.md) of order $q > 1$, with source groups $G_1$, $G_2$, target group $G_T$, exponent isomorphisms $\phi_1$, $\phi_2$, $\phi_T$ from $\mathbb{Z}/q\mathbb{Z}$ and pairing $e : G_1 \times G_2 \to G_T$. Let $t$ be a natural number, the degree parameter of the q-SDH problem (written $t$ because $q$ is the group order). For a q-SDH adversary $A$ as in the [win experiment](sdh-win.md), the q-SDH game draws the secret $x$ uniformly from the group of units $(\mathbb{Z}/q\mathbb{Z})^\times$, runs the win experiment at $x$, and outputs its result.

Boneh and Boyen also draw the generators at random; this game uses the fixed generators $g_1 = \phi_1(1)$ and $g_2 = \phi_2(1)$ of the interface. At prime order $p$ the units are the nonzero residues, so $x$ is uniform in $(\mathbb{Z}/p\mathbb{Z})^\times$, as in the source. The source states the experiment at prime order only; at composite $q$ the game keeps the input tuple and the pairing check and draws $x$ from the units of $\mathbb{Z}/q\mathbb{Z}$, and the check then rejects every $c$ for which $x + c$ is not a unit, $c = -x$ included.

## Sources

- D. Boneh and X. Boyen, *Short Signatures Without Random Oracles and the SDH Assumption in Bilinear Groups*, J. Cryptology 21 (2008), §3.1.
