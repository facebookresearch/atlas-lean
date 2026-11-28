# Base-change morphism on sections

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

Let $F$ be a sheaf of modules on $X$, let $\beta_F : \psi^* \pi_* F \to \pi'_* g'^* F$ be the base-change morphism, and let $\eta^{\psi}$ and $\eta^{g'}$ be the units of $\psi^* \dashv \psi_*$ and $g'^* \dashv g'_*$. For every open $U \subseteq T$, the two maps

$$
F(\pi^{-1} U) \longrightarrow (g'^* F)\bigl((\psi \circ \pi')^{-1} U\bigr)
$$

agree: the first is the component of $\eta^{\psi}_{\pi_* F}$ on $U$, a map $F(\pi^{-1}U) \to (\psi^*\pi_*F)(\psi^{-1}U)$, followed by $\beta_F$ on the open $\psi^{-1} U$; the second is the component of $\eta^{g'}_F$ on $\pi^{-1} U$, a map $F(\pi^{-1}U) \to (g'^*F)\bigl((\pi\circ g')^{-1}U\bigr)$, followed by the restriction map of $g'^* F$ along the equality of opens $(\psi \circ \pi')^{-1} U = (\pi \circ g')^{-1} U$ given by the square.
