# Integrated advection-diffusion-reaction balance

Let $c(t, x)$ be a concentration and $U$, $D$, $k$ real constants; fix $a$, $b$ and $t$, and write $J(t, x) = U c(t, x) - D\,\partial_x c(t, x)$. Assume that at every $x$ in the closed interval between $a$ and $b$ the functions $c(t, \cdot)$ and $\partial_x c(t, \cdot)$ are differentiable, with derivatives $\partial_x c$ and $\partial_{xx} c$, and that $\partial_t c + U \partial_x c = D \partial_{xx} c - k c$ holds there. Assume also that $c(t, \cdot)$, $\partial_x c(t, \cdot)$ and $\partial_{xx} c(t, \cdot)$ are interval integrable between $a$ and $b$. Then, with oriented integrals,

$$\int_a^b \partial_t c(t, x)\,dx = J(t, a) - J(t, b) - k \int_a^b c(t, x)\,dx.$$

For $a \le b$ this is the net inflow into $[a, b]$ minus the decayed amount.
