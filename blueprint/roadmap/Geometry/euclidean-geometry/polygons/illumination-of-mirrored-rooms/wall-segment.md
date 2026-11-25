# Walls of a polygonal room

For a cyclic list of points $v_0, \dots, v_{n-1} \in \mathbb{R}^2$ and an index $i$, the wall beginning at vertex $i$ is the closed segment

$$[v_i, v_{(i+1) \bmod n}] = \{(1 - t) v_i + t\, v_{(i+1) \bmod n} : t \in [0, 1]\}.$$
