# Interface flux with hydrostatic reconstruction

Given a numerical flux $\mathcal F$, a left cell with depth $h_L$, velocity $u_L$ on bed $z_L$, and a right cell with $h_R$, $u_R$ on bed $z_R$, set the face bed $z^* = \max(z_L, z_R)$ and the reconstructed depths $h_L^* = \max(0, h_L + z_L - z^*)$, $h_R^* = \max(0, h_R + z_R - z^*)$. The interface flux is defined as

$$F = \mathcal F\big((h_L^*, h_L^* u_L),\,(h_R^*, h_R^* u_R)\big).$$
