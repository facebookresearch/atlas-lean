# Weight of a walk in the two-squares visibility graph

Consider the closed squares $O_1 = [0,1] \times [0,1]$ and $O_2 = [2,3] \times [0,1]$ in the Euclidean plane $\mathbb{R}^2$ and the free set $G = \mathbb{R}^2 \setminus \operatorname{int}(O_1 \cup O_2)$. The ten graph vertices and their coordinates are $s = (-1, \tfrac12)$, $t = (4, \tfrac12)$, and the obstacle corners $A = (0,0)$, $B = (1,0)$, $C = (1,1)$, $D = (0,1)$, $E = (2,0)$, $F = (3,0)$, $P = (3,1)$, $Q = (2,1)$. The visibility graph is the simple graph on these vertices in which two distinct vertices are adjacent when the closed segment between their coordinates lies in $G$. The weight of a walk $v_0, v_1, \dots, v_k$ in this graph is the Euclidean length of the polyline through the coordinates of its vertices,

$$\sum_{i=0}^{k-1} \| v_i - v_{i+1} \| ,$$

which is $0$ for a walk of length zero.
