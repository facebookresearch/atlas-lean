# Horizontal pasting of base-change morphisms

Let two horizontally adjacent commutative squares of schemes be given by morphisms $\pi : X \to T$, $\psi : T' \to T$, $\pi' : X' \to T'$, $g' : X' \to X$ with $\pi \circ g' = \psi \circ \pi'$, and $\psi' : T'' \to T'$, $\pi'' : X'' \to T''$, $g'' : X'' \to X'$ with $\pi' \circ g'' = \psi' \circ \pi''$, so that the outer square satisfies $\pi \circ (g' \circ g'') = (\psi \circ \psi') \circ \pi''$. For a morphism $h$ write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules. Let $\beta_1$, $\beta_2$ and $\beta$ be the base-change morphisms of the first square, the second square and the outer square.

For every sheaf of modules $F$ on $X$, the base-change morphism $\beta_F : (\psi \circ \psi')^* \pi_* F \to \pi''_* (g' \circ g'')^* F$ equals the composite

$$
(\psi \circ \psi')^* \pi_* F \xrightarrow{\ \sim\ } \psi'^* \psi^* \pi_* F \xrightarrow{\ \psi'^*(\beta_{1,F})\ } \psi'^* \pi'_* g'^* F \xrightarrow{\ \beta_{2,\, g'^* F}\ } \pi''_* g''^* g'^* F \xrightarrow{\ \sim\ } \pi''_* (g' \circ g'')^* F,
$$

where the first map is the inverse of the pullback-composition isomorphism for $\psi'$ and $\psi$ at $\pi_* F$, and the last is $\pi''_*$ applied to the pullback-composition isomorphism for $g''$ and $g'$ at $F$.
