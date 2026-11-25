# Pullback two-square of a commutative square of schemes

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

The pullback two-square attached to the square is the natural transformation of functors from sheaves of modules on $T$ to sheaves of modules on $X'$

$$
\pi'^* \circ \psi^* \;\cong\; (\psi \circ \pi')^* \;=\; (\pi \circ g')^* \;\cong\; g'^* \circ \pi^*,
$$

the composite of the pullback-composition isomorphism for $\pi'$ and $\psi$, the isomorphism of pullbacks induced by the equality $\psi \circ \pi' = \pi \circ g'$, and the inverse of the pullback-composition isomorphism for $g'$ and $\pi$.
