# Base-change morphism and the unit

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

Let $M$ be a sheaf of modules on $T$, let $\beta$ denote the base-change morphism, let $\alpha : \pi'^* \psi^* \Rightarrow g'^* \pi^*$ be the pullback two-square of the square, and let $\eta$ and $\eta'$ be the units of $\pi^* \dashv \pi_*$ and $\pi'^* \dashv \pi'_*$. Then the two morphisms $\psi^* M \to \pi'_* g'^* \pi^* M$ agree:

$$
\beta_{\pi^* M} \circ \psi^*(\eta_M) = \pi'_*(\alpha_M) \circ \eta'_{\psi^* M}.
$$
