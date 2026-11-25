# The reciprocal basis is the unique dual basis

Let $\Lambda$ be a Bravais lattice with basis matrix $B$ ($\det B \ne 0$), primitive vectors $a_0, a_1, a_2$ (the columns of $B$) and lattice $L = \{Bn : n \in \mathbb{Z}^3\}$. Its reciprocal lattice $\Lambda^*$ has basis matrix $B^* = (2\pi/\det B)\,X(B)$, where $X(B)$ has columns $a_1 \times a_2$, $a_2 \times a_0$, $a_0 \times a_1$; its primitive vectors are $b_j = (2\pi/\det B)\,(a_{j+1} \times a_{j+2})$ (indices mod 3). For every real $3 \times 3$ matrix $M$, $B^* = M$ if and only if $B^{\mathsf T} M = 2\pi I$.
