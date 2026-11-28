# Metric learning pairwise kernel

**Definition (Eq. 5).** Let $K$ be a positive definite kernel on genes with feature map $\Phi$, $K(x,x')=\langle\Phi(x),\Phi(x')\rangle$. The metric learning pairwise kernel (MLPK) on pairs of genes is

$$K_{\mathrm{MLPK}}\bigl((x_1,x_2),(x_3,x_4)\bigr)=\bigl(K(x_1,x_3)-K(x_1,x_4)-K(x_2,x_3)+K(x_2,x_4)\bigr)^2=\bigl\langle\Phi(x_1)-\Phi(x_2),\Phi(x_3)-\Phi(x_4)\bigr\rangle^2.$$

**Properties.**

- $K_{\mathrm{MLPK}}$ is positive definite: it is the Frobenius inner product $\langle D_{12},D_{34}\rangle_{\mathrm{Fro}}$ of the rank-one operators $D_{ab}=(\Phi(x_a)-\Phi(x_b))(\Phi(x_a)-\Phi(x_b))^\top$.
- It is invariant under swapping the elements of either pair, so it is a positive definite kernel on unordered pairs, as needed for undirected interaction networks.
- Training an SVM on pairs with $K_{\mathrm{MLPK}}$, without the constraint $M\succeq0$, is the relaxation of positive semidefinite metric learning: by the representer theorem the learned metric is $d_M(x,x')=\sum_{(i,j)}\alpha_{ij}\langle\Phi(x)-\Phi(x'),\Phi(x_i)-\Phi(x_j)\rangle^2$, and an edge is predicted for pairs at small learned distance.

It differs from the tensor product pairwise kernel $K_{\mathrm{TPPK}}=K(x_1,x_3)K(x_2,x_4)+K(x_1,x_4)K(x_2,x_3)$ (Eq. 4), which compares the members of two pairs individually, whereas MLPK compares the pairs only through the differences of their members.

## Depends on

- [Representer theorem for positive semidefinite metric learning](representer-theorem-for-positive-semidefinite-metric-learning.md)

## Expansion

With finite-dimensional features, $\langle D_{12},D_{34}\rangle_{\mathrm{Fro}}=\mathrm{Tr}(u_{12}u_{12}^\top u_{34}u_{34}^\top)=(u_{12}^\top u_{34})^2$, and expanding $u^\top u'$ in kernel values gives the formula. Substituting the expansion of $M$ from the representer theorem into the metric learning problem expresses $d_M$ and $\|M\|_{\mathrm{Fro}}^2$ through $K_{\mathrm{MLPK}}$ evaluated on training pairs; dropping the semidefiniteness constraint leaves a standard SVM in this kernel. Sums of kernels for different data types (expression, phylogenetic profiles, localization, interaction graphs) give a single MLPK for heterogeneous data.

## Sources

- J.-P. Vert, J. Qiu, W. S. Noble, "A new pairwise kernel for biological network inference with support vector machines", BMC Bioinformatics 8 (Suppl 10) (2007) S8. <https://doi.org/10.1186/1471-2105-8-S10-S8>, PMCID PMC2230501. Eqs. (4)–(6) and the derivation following Theorem 1.
