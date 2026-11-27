# State-space model of a multi-zone thermal network

For finitely many zones $i$ with heat capacities $C_i$, inter-zone conductances $G_{ij}$ and conductances $g_{0,i}$ to the outside, the zone thermal plant is defined as the linear state-space system with state the zone temperatures $x$, input the outside temperature $T_{out}$ together with the zone heating powers $P$, and output the zone temperatures. Its matrices are

$$(Ax)_i = \frac{1}{C_i}\Big(\sum_j G_{ij}x_j - \Big(\sum_j G_{ij} + g_{0,i}\Big)x_i\Big), \qquad (Bu)_i = \frac{g_{0,i}T_{out} + P_i}{C_i},$$

$C = I$ and $D = 0$.
