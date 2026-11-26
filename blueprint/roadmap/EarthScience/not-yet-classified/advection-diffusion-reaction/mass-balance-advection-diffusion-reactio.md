# Mass balance for advection, diffusion and first-order decay

Let $c(t,x)$ satisfy $\partial_t c + U\,\partial_x c = D\,\partial_{xx} c - k\,c$ at time $t$ for every $x$ between $a$ and $b$ (in either order). Assume that at time $t$ the functions $c$, $\partial_x c$ and $\partial_{xx} c$ are interval integrable between $a$ and $b$, that $c$ and $\partial_x c$ are differentiable in $x$ at every point between $a$ and $b$, and that $\frac{d}{dt}\int_a^b c\,dx = \int_a^b \partial_t c\,dx$ at $t$. Then, with the flux $J(t,x) = U\,c(t,x) - D\,\partial_x c(t,x)$,

$$\frac{d}{dt}\int_a^b c(t,x)\,dx = J(t,a) - J(t,b) - k\int_a^b c(t,x)\,dx.$$

For $a \le b$ this is the mass on $[a,b]$ changing by net inflow minus decay; for $b < a$ both sides are the negatives of the balance on $[b,a]$.
