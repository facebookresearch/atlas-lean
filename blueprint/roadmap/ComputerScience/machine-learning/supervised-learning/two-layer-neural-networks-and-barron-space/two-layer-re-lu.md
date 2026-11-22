# Two-layer ReLU network

**Two-layer ReLU network** of width $m$ without bias: $f(x; \theta) = \sum_k a_k \max(\langle w_k, x \rangle, 0)$
for outer weights $a_1, \dots, a_m \in \mathbb{R}$ and inner weights $w_1, \dots, w_m \in \mathbb{R}^d$
(W. E, C. Ma and L. Wu, *A priori estimates of the population risk for two-layer neural networks*,
Commun. Math. Sci. 17 (2019), equation (3.1), with the ReLU activation).
