# Positive steady states of mass-conserving single terminal-linkage networks

**Setting.** $m$ species and $n$ complexes; $Y\in\mathbb{R}_{\ge0}^{m\times n}$ has column $y_j$ = complex $j$. The reaction graph has weighted adjacency matrix $A$ with $A_{ij}=k_{i\to j}>0$ for each reaction, $D=\operatorname{diag}(A\mathbf 1)$ and $A_k=A^{\mathsf T}-D$ (so $\mathbf 1^{\mathsf T}A_k=0$). With mass-action monomials $\psi_j(c)=\prod_i c_i^{Y_{ij}}$ and a vector $b\in\mathbb{R}^m$ of exchange fluxes across the boundary, the dynamics is

$$
\dot c=YA_k\psi(c)-b ,
$$

and a steady state is a pair $(c,v)$ with flux balance $YA_kv=b$ and mass action $v=\psi(c)$, equivalently $Y^{\mathsf T}\log c=\log v$ for $c>0$. The network is **mass conserving** if $e^{\mathsf T}YA_k=0$ for some positive vector $e$ (molecular weights); a **terminal-linkage class** is a strongly connected set of complexes, and a **single terminal-linkage network** is one whose reaction graph is a single strongly connected component.

**Theorem (Akle et al., Theorem 2).** Let the network be mass conserving and consist of a single terminal-linkage class, with arbitrary rate constants $k>0$. Then there is a concentration vector $c>0$ with

$$
YA_k\psi(c)=b
$$

if and only if $b$ lies in the range of $YA_k$. In particular ($b=0$) every such closed network has a positive equilibrium, whatever its deficiency and whether or not it is complex balanced.

The positivity step rests on two lemmas: the minimizer of the convex fixed-point problem has the largest support among feasible points (Lemma 1), and for a single terminal-linkage class the problem parameterized by a fixed point has a strictly positive feasible point (Lemma 2); hence the fixed point is positive and solves $Y^{\mathsf T}\log c=\log v$, $YA_kv=v_0b$ with $v_0>0$.

## Depends on

- [Convex fixed-point map for mass-action steady states](convex-fixed-point-map-for-mass-action-steady-states.md)

## Expansion

Necessity of $b\in\operatorname{range}(YA_k)$ is immediate. For sufficiency the fixed-point construction yields $c>0$ and $\alpha=v_0>0$ with $YA_k\psi(c)=\alpha b$. To remove $\alpha$: mass conservation says $Y^{\mathsf T}e\in\ker A_k^{\mathsf T}$, and for a strongly connected graph this kernel is spanned by $\mathbf 1$, so $\mathbf 1=Y^{\mathsf T}\delta$ for some $\delta$. Setting $\log\tilde c=\log c-(\log\alpha)\delta$ gives $\psi(\tilde c)=\psi(c)/\alpha$ and hence $YA_k\psi(\tilde c)=b$. The result goes beyond the deficiency-zero and deficiency-one theorems and covers open systems with prescribed exchange fluxes; numerical experiments suggest it extends to several terminal-linkage classes.

## Sources

- S. Akle, O. Dalal, R. M. T. Fleming, M. Saunders, N. Taheri, Y. Ye, "Existence of positive steady states for mass conserving and mass-action chemical reaction networks with a single terminal-linkage class", arXiv:1105.2359 (2011). <https://doi.org/10.48550/arXiv.1105.2359>
