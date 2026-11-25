# Loaded closed-loop transfer

Let $A_0, \omega_p, \beta, a, b \in \mathbb{R}$, $s, v_i, v_o, v_{amp} \in \mathbb{C}$, and let $A(s) = A_0/(1 + s/\omega_p)$ be the one-pole open-loop gain. Assume $\omega_p \neq 0$, $1 + s/\omega_p \neq 0$ and $1 + s/\omega_p + \beta b A_0 \neq 0$. If

$$v_{amp} = A(s)\,(a v_i - \beta v_o) \quad\text{and}\quad v_o = b\, v_{amp},$$

then $v_o = G(s)\, v_i$, where

$$G(s) = \frac{a b A_0}{1 + s/\omega_p + \beta b A_0}.$$
