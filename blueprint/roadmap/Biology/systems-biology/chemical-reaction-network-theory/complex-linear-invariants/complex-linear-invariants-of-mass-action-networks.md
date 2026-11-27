# Complex-linear invariants of mass-action networks

**Setting.** A mass-action reaction network with species concentrations $x\in\mathbb R^n_{>0}$ and complexes $C_1,\dots,C_m$ has dynamics

$$\frac{dx}{dt}=f(x)=Y\cdot\mathcal L(G)\cdot\Psi(x),$$

where $Y$ is the $n\times m$ stoichiometric matrix of complexes, $\mathcal L(G)$ is the Laplacian of the labelled reaction graph on complexes (rate constants as edge labels), and $\Psi(x)=(x^{C_1},\dots,x^{C_m})$ is the vector of complex monomials. Put $M=Y\mathcal L(G)$. A *type 1 complex-linear invariant* on $C_1,\dots,C_k$ is a relation $\sum_{i\le k}a_i x^{C_i}=0$ that holds at every steady state and comes from a linear functional $a$ with $a\cdot B'=0$. Here $B$ is a matrix whose columns form a basis of $\ker M$, and $B'$ consists of its first $k$ rows.

**Theorem.**

1. The space $I_k$ of type 1 complex-linear invariants on $C_1,\dots,C_k$ has dimension $\dim I_k=k-\operatorname{rk}B'$.
2. Choose a set $U$ of $l=\operatorname{rk}B'$ linearly independent rows of $B'$, and let $V$ be the remaining $k-l$ rows. Then at every steady state

$$\Psi(x)_V=B'_V\,(B'_U)^{-1}\,\Psi(x)_U ,$$

and each of the $k-l$ rows of this matrix identity is an independent type 1 complex-linear invariant. The coefficients are rational functions of the rate constants and can be computed by linear algebra alone.
3. The method applies to bifunctional enzymes, whose networks have deficiency up to four, with the source's labelling of complexes and rate constants $k_i$. For the EnvZ/OmpR osmoregulator the invariants on four complexes combine, at every positive steady state with $[\text{EnvZ-ATP}] \ne 0$, into

$$[\text{OmpR-P}] = \frac{k_1k_3k_5(k_{11}+k_{12})(k_{14}+k_{15})}{k_1k_3k_{10}k_{12}(k_{14}+k_{15}) + k_2k_{13}k_{15}(k_4+k_5)(k_{11}+k_{12})},$$

so OmpR-P has absolute concentration robustness: its steady-state value does not depend on the amounts of OmpR or EnvZ. For the PFK-2/F-2,6-BPase glycolytic regulator one of the invariants is $k_5x_{C_4} - k_8x_{C_6} - k_{11}x_{C_8} + (k_{18} - k_{19})x_{C_{11}} = 0$; it gives a bound, not a fixed value: if $k_{18} > k_{19}$ the steady-state concentration of F6P is held below a level that depends only on the rate constants, and if $k_{18} < k_{19}$ the same holds for F2,6BP.

## Proof sketch

At steady state $\Psi(x)\in\ker M$, so $\Psi(x)=B\lambda$ for some $\lambda$, and any functional killing the first $k$ rows of $B$ kills $\Psi(x)$ restricted to those complexes. The construction is the dual of finding $\ker M$. It recovers earlier results: complex-balanced (Horn–Jackson) steady states for deficiency zero, and the Shinar–Feinberg absolute concentration robustness for deficiency-one networks with two non-terminal complexes differing in one species. When an invariant involves two complexes differing only in one species $S$, it fixes $[S]$ at every steady state, which is the absolute concentration robustness seen in bifunctional two-component systems. The method needs no restriction on deficiency, so it applies to realistic signalling networks.

## Sources

- Robert L. Karp, Mercedes Pérez Millán, Tathagata Dasgupta, Alicia Dickenstein and Jeremy Gunawardena, "Complex-linear invariants of biochemical networks", *Journal of Theoretical Biology* 311 (2012), 130–138, <https://doi.org/10.1016/j.jtbi.2012.07.004>. Preprint version: arXiv:1207.3453 (2012), Results section, Proposition 1 (dimension of $I_k$), Theorem 1 (invariants from the matrix identity), Corollaries 1–2 (EnvZ/OmpR and PFK-2/F-2,6-BPase invariants), <https://doi.org/10.48550/arXiv.1207.3453>.
