# Horizontal crossing probability of a box

Let $p_h, p_v \in \mathbb{R}$ and $a, b \in \mathbb{N}$. The horizontal crossing probability of the box $[0, a] \times [0, b]$ in anisotropic bond percolation is the total weight of the edge configurations of the box that contain an open horizontal crossing:

$$P_{p_h, p_v}(H(a, b)) = \sum_{\omega \in \{\text{open}, \text{closed}\}^{E}} \mathbf{1}[\omega \in H(a, b)]\, w_{p_h, p_v}(\omega),$$

where $E$ is the edge set of the box and $w_{p_h, p_v}(\omega)$ is the product of $p_h$ or $1 - p_h$ over horizontal edges and $p_v$ or $1 - p_v$ over vertical edges according as each edge is open or closed. Since $H(a, b)$ depends only on edges of the box, for $p_h, p_v \in [0, 1]$ this equals the probability of $H(a, b)$ in the infinite-lattice model.
