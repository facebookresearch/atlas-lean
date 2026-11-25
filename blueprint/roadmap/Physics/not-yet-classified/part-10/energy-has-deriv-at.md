# Energy flux identity for water hammer

Let $a, g, A, L > 0$. Let $h(t,x)$ and $q(t,x)$ have partial derivatives $h_t, h_x, q_t, q_x$ for $x \in [0, L]$ (one-sided in $x$ at the ends), with $h_t$ and $q_t$ continuous on $\mathbb R \times [0, L]$, and satisfy

$$h_t + \frac{a^2}{gA}\,q_x = 0, \qquad q_t + gA\,h_x = 0 \quad \text{on } [0, L].$$

Then the energy $E(t) = \int_0^L \Big(\frac{gA}{a^2}\frac{h^2}{2} + \frac{q^2}{2gA}\Big)dx$ satisfies

$$E'(t) = h(t,0)\,q(t,0) - h(t,L)\,q(t,L).$$

The physical energy carries an extra factor $\rho g$.
