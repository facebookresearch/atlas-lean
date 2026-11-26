# Components of the base-change transformation

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

For every sheaf of modules $F$ on $X$, the component at $F$ of the base-change natural transformation $\psi^* \pi_* \Rightarrow \pi'_* g'^*$ is the base-change morphism $\psi^* \pi_* F \to \pi'_* g'^* F$ (the two agree by definition).
