# Face Flux

For free-flow speed $v$, congested wave speed $w$, jam density $k_j$, upstream density $k_{up}$ and downstream density $k_{down}$, the face flux between the two cells is the smaller of upstream demand and downstream supply under the triangular fundamental diagram:

$$\min\bigl(\min(v k_{up}, C),\ \min(w(k_j - k_{down}), C)\bigr), \qquad C = \frac{v w k_j}{v + w},$$

with capacity $C = 0$ when $v + w = 0$, by the convention $x/0 = 0$.
