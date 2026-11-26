# Exact difference between reticulation-visible and tree-child network counts

**Setting.** A (binary) phylogenetic network on a leaf set $X$ with $|X|=\ell$ is a rooted directed acyclic graph without parallel edges whose root has in-degree $0$ and out-degree $1$, whose leaves have in-degree $1$ and out-degree $0$ and are bijectively labeled by $X$, and whose other vertices are tree nodes (in-degree $1$, out-degree $2$) or reticulations (in-degree $2$, out-degree $1$). It is *tree-child* if every non-leaf vertex has a child that is a tree node or a leaf, and *reticulation-visible* if for every reticulation $r$ there is a leaf $\lambda$ such that every root-to-$\lambda$ path passes through $r$. Write $TC_{\ell,k}$ and $RV_{\ell,k}$ for the numbers of tree-child and reticulation-visible networks with $\ell$ labeled leaves and $k$ reticulations, and

$$\Delta_k(\ell) := RV_{\ell,k} - TC_{\ell,k} \ge 0 .$$

**Statement.**

1. For $k=0,1$ the classes coincide: a network with exactly one reticulation is reticulation-visible if and only if it is tree-child, so $\Delta_0(\ell)=\Delta_1(\ell)=0$ for all $\ell\ge 2$.
2. For all $\ell\ge 3$,
$$\Delta_2(\ell) = \bigl(4\ell^3+3\ell^2-\ell-1\bigr)(2\ell-3)!! - (4\ell+1)\,2^{\ell-1}\,\ell! .$$
3. For all $\ell\ge 4$,
$$\Delta_3(\ell) = \frac{24\ell^5+50\ell^4-49\ell^3-80\ell^2+16\ell+12}{3}\,(2\ell-3)!! - \bigl(24\ell^3+8\ell^2-27\ell-22\bigr)\,2^{\ell-2}\,\ell! .$$

For example $TC_{3,2}=42$ and $\Delta_2(3)=81$, $TC_{4,3}=2544$ and $\Delta_3(4)=17916$.

## Expansion

The case $k=1$ is structural: with one reticulation $r$, its unique child cannot be a reticulation, so tree-child holds; conversely the tree-child property gives a leaf reachable from $r$ through tree nodes only, and since $r$ is the only in-degree-$2$ vertex every root path to that leaf passes through $r$.

For $k=2,3$ the formulas follow by subtracting two proven closed forms. The tree-child count is $TC_{\ell,k}=\frac{\ell!}{(\ell-k)!}\,c_{\ell-1,k}$, where $c_{n,k}$ counts constrained words (equivalently, $\mathbf c_n = A_n \mathbf c_{n-1}$ for the lower-triangular matrix with entries $a_{ij}=2n+j-1$, $j\le i$), giving for instance
$TC_{\ell,2} = \binom{\ell}{2}\bigl[(2\ell+1)!!-2(2\ell)!!+\tfrac13(2\ell-1)!!\bigr]$. The reticulation-visible counts come from the component-graph decomposition (a network is reticulation-visible if and only if its component graph is tree-child) and have the same shape $A(\ell)(2\ell-3)!! - B(\ell)2^{\ell-c}\ell!$. Rewriting $(2\ell+2j+1)!!$ and $(2\ell+2j)!!=2^{\ell+j}(\ell+j)!$ in the two base factors $(2\ell-3)!!$ and $2^{\ell-1}\ell!$ and collecting coefficients yields the stated polynomials. The identities can be checked by exact arithmetic against the tree-child recursion.

## Sources

- Josep Batle, "Exact Enumeration of Phylogenetic Networks: The Tree-Child, Reticulation-Visible and Orchard Hierarchy", arXiv:2606.24325 (2026), Lemma 4.1, Proposition 4.2, Theorem 4.3 and Theorem 4.5, <https://doi.org/10.48550/arXiv.2606.24325>
