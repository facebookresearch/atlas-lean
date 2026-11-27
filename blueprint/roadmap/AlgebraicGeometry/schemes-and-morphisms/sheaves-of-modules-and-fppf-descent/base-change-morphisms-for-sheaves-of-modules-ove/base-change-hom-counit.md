# Base-change morphism and the counit

Consider a commutative square of schemes

$$
\begin{array}{ccc} X' & \xrightarrow{\ g'\ } & X \\ {\scriptstyle \pi'}\downarrow & & \downarrow{\scriptstyle \pi} \\ T' & \xrightarrow{\ \psi\ } & T \end{array} \qquad \pi \circ g' = \psi \circ \pi'.
$$

For a morphism of schemes $h$, write $h^*$ and $h_*$ for pullback and pushforward of sheaves of modules, with the adjunction $h^* \dashv h_*$.

Let $F$ be a sheaf of modules on $X$, let $\beta_F : \psi^* \pi_* F \to \pi'_* g'^* F$ be the base-change morphism, let $\alpha : \pi'^* \psi^* \Rightarrow g'^* \pi^*$ be the pullback two-square of the square, and let $\varepsilon$ and $\varepsilon'$ be the counits of $\pi^* \dashv \pi_*$ and $\pi'^* \dashv \pi'_*$. Then the two morphisms $\pi'^* \psi^* \pi_* F \to g'^* F$ agree:

$$
\varepsilon'_{g'^* F} \circ \pi'^*(\beta_F) = g'^*(\varepsilon_F) \circ \alpha_{\pi_* F}.
$$
