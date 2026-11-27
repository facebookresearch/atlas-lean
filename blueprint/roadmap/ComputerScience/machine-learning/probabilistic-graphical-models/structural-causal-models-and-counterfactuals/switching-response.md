# Switching-response causal model

The switching-response model is the binary structural causal model on $X \to Y$ with noise $u = (u_X, u_Y) \in \{0,1\}^2$, uniform weights $p_U(u) = 1/4$, and structural equations $X = u_X$ and $Y = X$ if $u_Y = 1$ (the type "helped"), $Y = 1 - X$ if $u_Y = 0$ (the type "hurt").
