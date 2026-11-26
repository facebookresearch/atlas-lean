# Naturality of the base-change morphism

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

For every morphism $\varphi : F \to G$ of sheaves of modules on $X$, writing $\beta_F : \psi^* \pi_* F \to \pi'_* g'^* F$ for the base-change morphism,

$$
\beta_G \circ \psi^*(\pi_* \varphi) = \pi'_*(g'^* \varphi) \circ \beta_F .
$$
