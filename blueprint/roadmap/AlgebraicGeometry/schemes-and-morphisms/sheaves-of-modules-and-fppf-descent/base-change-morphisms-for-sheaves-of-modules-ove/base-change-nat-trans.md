# Base-change natural transformation for sheaves of modules

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

The base-change natural transformation is the natural transformation

$$
\psi^* \circ \pi_* \Longrightarrow \pi'_* \circ g'^*
$$

of functors from sheaves of modules on $X$ to sheaves of modules on $T'$, defined as the mate of the pullback two-square $\pi'^* \psi^* \Rightarrow g'^* \pi^*$ of the square under the adjunctions $\pi^* \dashv \pi_*$ and $\pi'^* \dashv \pi'_*$.
