# Likelihood equivalence classes of circular genomes under symmetric rearrangement models

**Setting.** A circular genome with $N\ge3$ regions is a permutation $\sigma\in S_N$ ($\sigma(i)=j$: region $i$ sits at position $j$ in a fixed reference frame). Rotations and flips of the circle form the dihedral group $D_N\subset S_N$ of order $2N$, and $\sigma$ and $d\sigma$ ($d\in D_N$) represent the same physical genome. A **biological model** $(\mathcal M,w)$ is a set of rearrangements $\mathcal M\subseteq S_N\setminus D_N$ (for example inversions) with probabilities $w:\mathcal M\to(0,1]$, $\sum_{a\in\mathcal M}w(a)=1$; a rearrangement acts by $\sigma\mapsto a\sigma$, and events occur independently in time (for instance as a Poisson process of rate $1$). The **path probability** that the identity genome reaches the genome of $\sigma$ in $k$ events is

$$\alpha_k(\sigma)=\sum_{d\in D_N}\ \sum_{\substack{(a_1,\dots,a_k)\in\mathcal M^k\\ a_k\cdots a_1=d\sigma}}w(a_1)\cdots w(a_k),$$

and the likelihood of elapsed time $T$ is $L(T\mid\sigma)=\sum_{k\ge0}\alpha_k(\sigma)\,\mathbb P(k\text{ events in time }T)$; its maximiser is a rearrangement distance.

The model has **dihedral symmetry** if $d\mathcal Md^{-1}=\mathcal M$ and $w(dad^{-1})=w(a)$ for all $d\in D_N$, $a\in\mathcal M$; it is **time reversible** if $\mathcal M=\mathcal M^{-1}$ and $w(a^{-1})=w(a)$. Two permutations are **$(\mathcal M,w)$-equivalent** if their likelihood functions coincide, which holds iff $\alpha_k(\sigma_1)=\alpha_k(\sigma_2)$ for all $k$.

**Theorem.**
1. For every model, $\sigma$ is equivalent to every element of $[\sigma]=\{d\sigma:d\in D_N\}$, and there are exactly $N!/(2N)=(N-1)!/2$ such classes.
2. With dihedral symmetry, $\alpha_k(d_1\sigma d_2)=\alpha_k(\sigma)$ for all $d_1,d_2\in D_N$, so the classes contain $[\sigma]_D=\{d_1\sigma d_2:d_1,d_2\in D_N\}$; their number equals the number $S(N)$ of similarity classes of $N$-vertex polygons inscribed on $N$ equally spaced points of a circle (polygons up to rotation and reflection).
3. With dihedral symmetry and time reversibility, additionally $\alpha_k(\sigma^{-1})=\alpha_k(\sigma)$, so the classes contain $[\sigma]_{DR}=[\sigma]_D\cup[\sigma^{-1}]_D$; their number equals the number $T(N)$ of equivalence classes of $N\times N$ permutation matrices under cyclic shifts of rows or columns, rotations and transposition. In this case the maximum likelihood distance is symmetric.

Neither symmetry implies the other: for $N\ge5$ the conjugates of $a=(1,2,4,3)$ and $b=(1,2)$ by $D_N$ give a dihedrally symmetric model that is not time reversible, and with $N=6$, $\mathcal M=\{(1,2),(2,3),(3,4),(4,5),(5,6)\}$ and uniform weights the model is reversible but $\alpha_4\big((1,2,4,3)\big)=11/5^4\neq8/5^4=\alpha_4\big((1,3,4,2)\big)$.

## Expansion

Statement 1 holds because $\alpha_k$ already sums over the $2N$ representatives of the target genome, and $D_N$ acts freely on $S_N$ by left multiplication. For 2, conjugating a path $a_k\cdots a_1=\tau$ by $d$ gives a path $(da_kd^{-1})\cdots(da_1d^{-1})=d\tau d^{-1}$ with the same weight, so $\beta_k(d\tau d^{-1})=\beta_k(\tau)$ for the single-target path probabilities $\beta_k$; combining with the sum over left cosets gives invariance under $\sigma\mapsto d_1\sigma d_2$. For 3, reversing and inverting a path $a_k\cdots a_1=\tau$ gives $a_1^{-1}\cdots a_k^{-1}=\tau^{-1}$ with the same weight. The counting statements identify the double-coset orbits with polygons (draw the edge $i\to i+1$ between the positions of consecutive regions) and with permutation matrices (inversion is transposition, and dihedral actions are cyclic shifts and reflections of rows and columns). In computations the dihedral sum can be moved inside the group-algebra representation, reducing the work per irreducible representation.

## Sources

- Venta Terauds and Jeremy Sumner, "Circular genome rearrangement models: applying representation theory to evolutionary distance calculations", arXiv:1712.00858 (2017), Section 2; Section 3, Definitions 3.1 and 3.5, Examples 3.2 and 3.4, Proposition 3.3, Corollary 3.6; Section 3.1, Propositions 3.7, 3.9 and 3.11. <https://doi.org/10.48550/arXiv.1712.00858>
