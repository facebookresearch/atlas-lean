# Hessian-determinant invariants of rank-$n$ tensors

**Setting.** Let $P$ be an $n\times n\times n$ complex tensor, acted on by $G=GL(n,\mathbb C)^3$ through its three indices: $P(g_1,g_2,g_3)$. For a vector $\mathbf v$ write $P*_i\mathbf v$ for the $n\times n$ matrix obtained by contracting the $i$-th index of $P$ with $\mathbf v$. Let $D=\sum_{i=1}^n\mathbf e_i\otimes\mathbf e_i\otimes\mathbf e_i$ be the diagonal identity tensor and $\mathcal D$ its $G$-orbit.

**Orbit characterization (Section 2).** $\mathcal D$ is exactly the set of tensors of complex tensor rank $n$ and multilinear rank $(n,n,n)$. Its closure $V_n$ is the variety of tensors of border rank at most $n$; $V_n$ also contains tensors of rank larger than $n$.

**Commutation relations (Section 3).** Polynomials vanishing on $V_n$ include the entries of

$$(P*_i\mathbf e_j)\,\operatorname{adj}(P*_i\mathbf v)\,(P*_i\mathbf e_k)-(P*_i\mathbf e_k)\,\operatorname{adj}(P*_i\mathbf v)\,(P*_i\mathbf e_j)=0,$$

for $i=1,2,3$, $1\le j<k\le n$ and arbitrary $\mathbf v$, where $\operatorname{adj}$ is the classical adjoint.

**The invariants.** With a vector $\mathbf x=(x_1,\dots,x_n)$ of indeterminates define

$$h_i(P;\mathbf x)=\det(P*_i\mathbf x), \qquad f_i(P;\mathbf x)=(-1)^{n-1}\det\bigl(H_{\mathbf x}\,h_i(P;\mathbf x)\bigr),$$

where $H_{\mathbf x}$ is the Hessian in $\mathbf x$. Then $f_i$ has degree $n^2$ in $P$ and $n(n-2)$ in $\mathbf x$, transforms as $f_i(P';\mathbf x)=\det(g_j)^n\det(g_k)^n\det(g_i)^2 f_i(P;g_i\mathbf x)$ for $P'=P(g_1,g_2,g_3)$, satisfies $f_i(D;\mathbf x)=(n-1)(x_1\cdots x_n)^{n-2}$, and for $n=2$ equals Cayley's $2\times2\times2$ hyperdeterminant.

**Theorem (Section 4).** $P\in\mathcal D$ if and only if, for some $i\in\{1,2,3\}$, $P$ satisfies the commutation relations and $f_i(P;\mathbf x)$ is not the zero polynomial in $\mathbf x$; if this holds for one $i$ it holds for all. Equivalently, $P\in\mathcal D$ if and only if $P\in V_n$ and $f_i(P;\mathbf x)\neq 0$.

So the non-vanishing of one explicit polynomial family separates the generic rank-$n$ tensors from the lower-dimensional strata of $V_n$, giving a semialgebraic description of $\mathcal D$.

## Expansion

Invariance of $\mathcal D$ under $G$ plus the transformation law of $f_i$ and its value at $D$ give necessity. For sufficiency, $f_i\ne 0$ forces some linear combination of $i$-slices to be non-singular, since otherwise $h_i\equiv 0$. A tensor in the commutation variety with a non-singular slice combination is $G$-equivalent to one with simultaneously upper-triangular slices; if some slice had zero diagonal, $h_i$ would not depend on one coordinate of $\mathbf x$, the Hessian would have a zero row, and $f_i$ would vanish. With all diagonals non-zero the triangular representative lies in the orbit of $D$. In phylogenetics $V_n$ is the Zariski closure of the leaf distributions of the $n$-state general Markov model on a $3$-leaf tree, and the commutation relations are the corresponding phylogenetic invariants, alongside [edge-flattening rank conditions](../phylogenetic-invariants/flattening-rank-bound-for-the-general-markov-model.md) for larger trees.

## Depends on

- [Edge flattenings of the general Markov model have rank at most the number of states](../phylogenetic-invariants/flattening-rank-bound-for-the-general-markov-model.md)

## Sources

- Elizabeth S. Allman, Peter D. Jarvis, John A. Rhodes and Jeremy G. Sumner, "Tensor rank, invariants, inequalities, and applications", arXiv:1211.3461 (2012), Sections 2–4 (orbit proposition, commutation relations, construction of $f_i$ and the characterization theorem with its corollaries), <https://doi.org/10.48550/arXiv.1211.3461>. Published version: SIAM Journal on Matrix Analysis and Applications 34(3) (2013), 1014–1045, <https://doi.org/10.1137/120899066>; locators above refer to the arXiv version.
