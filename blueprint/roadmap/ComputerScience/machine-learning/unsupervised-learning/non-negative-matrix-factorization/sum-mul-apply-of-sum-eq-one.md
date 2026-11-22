# Mutational signatures

**Mutational signatures** (Alexandrov et al. 2013). Write the mutation-count matrix
(mutation types × samples) as $W H$, signatures (the columns of $W \in \mathbb{R}^{m \times k}$,
with $m, k$ finite) times exposures $H \in \mathbb{R}^{k \times n}$. If every column of $W$ sums to
$1$ (for instance a probability vector over mutation types), the total count
$\sum_i (W H)_{ij}$ of sample $j$ equals the sum $\sum_a H_{aj}$ of its exposures.
