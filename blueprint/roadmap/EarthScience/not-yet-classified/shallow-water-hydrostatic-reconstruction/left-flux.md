# Left numerical flux

Let $g$ be gravity, $\mathcal F$ a numerical flux on conserved pairs, and consider a left cell with depth $h_L$, velocity $u_L$, bed $z_L$ and a right cell with $h_R$, $u_R$, $z_R$. With face bed $z^* = \max(z_L, z_R)$, reconstructed depths $h_L^* = \max(0, h_L + z_L - z^*)$ and $h_R^* = \max(0, h_R + z_R - z^*)$, and face states $U_L^* = (h_L^*, h_L^* u_L)$, $U_R^* = (h_R^*, h_R^* u_R)$, the left numerical flux is

$$\mathcal F_l = \mathcal F(U_L^*, U_R^*) + \big(0,\ g h_L^2/2 - g (h_L^*)^2/2\big).$$

The left cell uses it at its right face.
