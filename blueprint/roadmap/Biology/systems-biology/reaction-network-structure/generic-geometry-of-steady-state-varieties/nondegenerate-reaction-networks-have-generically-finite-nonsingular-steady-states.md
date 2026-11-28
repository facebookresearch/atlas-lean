# Nondegenerate reaction networks have generically finite, nonsingular steady states

**Setting.** A reaction network with $n$ species and $m$ reactions under power-law (generalized mass-action) kinetics has stoichiometric matrix $N \in \mathbb{R}^{n\times m}$, integer kinetic exponent matrix $M \in \mathbb{Z}^{n \times m}$ (the source assumes integer exponents and notes that rational exponents reduce to this case; Theorem B(iii) is not defined for real exponents) and rate constants $\kappa \in \mathbb{R}^m_{>0}$, so $\dot x = N(\kappa \circ x^M)$ with $x^M = (x^{M_{\cdot 1}}, \dots, x^{M_{\cdot m}})$. The rows of $L \in \mathbb{R}^{d\times n}$ span the left kernel of $N$ (conservation laws $Lx = b$). Positive steady states with total amounts $b$ are the positive zeros $\mathbb{V}_{>0}(F_{\kappa,b})$ of

$$F_{\kappa,b}(x) = \begin{pmatrix} N(\kappa\circ x^M) \\ Lx - b\end{pmatrix}.$$

The network is *nondegenerate* if some $F_{\kappa,b}$ has a positive zero with nonsingular Jacobian; equivalently $\ker N \cap \mathbb{R}^m_{>0} \ne \varnothing$ and

$$\operatorname{rk}\begin{bmatrix} N\operatorname{diag}(w)M^\top\operatorname{diag}(h) \\ L \end{bmatrix} = n \quad\text{for some } (w,h) \in \ker N \times (\mathbb{C}^*)^n .$$

Let $Z_{cc} = \{(\kappa, b) : \mathbb{V}_{>0}(F_{\kappa,b}) \ne \varnothing\}$.

**Theorem A (dichotomy).** Assume $\ker N \cap \mathbb{R}^m_{>0} \ne \varnothing$.
- If the network is nondegenerate, $Z_{cc}$ has nonempty interior, and for generic $(\kappa,b) \in Z_{cc}$ the set $\mathbb{V}_{>0}(F_{\kappa,b})$ is finite and the Jacobian of $F_{\kappa,b}$ is nonsingular at each of its points.
- If the network is degenerate, $Z_{cc}$ is nonempty with empty interior, and the Jacobian is singular at every positive steady state for every $(\kappa,b) \in Z_{cc}$.

**Theorem B (absolute concentration robustness).** For a nondegenerate network the following are equivalent: (i) generic local ACR for species $X_i$; (ii) $\operatorname{rk}\big((N\operatorname{diag}(w)M^\top)_{\setminus i}\big) < \operatorname{rk} N$ for all $w \in \ker N$, where ${\setminus i}$ removes the $i$-th column; (iii) the saturation $\big(\langle N(\kappa \circ x^M)\rangle : (x_1\cdots x_n)^\infty\big)$ contains a nonconstant polynomial in $\mathbb{R}(\kappa)[x_i]$. The network has generic ACR for $X_i$ if that polynomial has a single positive root for generic $\kappa$.

**Theorem C (nondegenerate multistationarity).** If a nondegenerate network admits multistationarity and $\mathbb{V}_{>0}(F_{\kappa,b})$ is finite for all $(\kappa,b)$, then it admits nondegenerate multistationarity: some $(\kappa, b)$ has at least two positive steady states, all with nonsingular Jacobian. This is the case $\ell = 2$ of the Nondegeneracy Conjecture for nondegenerate networks.

## Depends on

- [Nondegeneracy Conjecture for reaction networks](../../nondegeneracy-conjecture-for-reaction-networks.md)

## Expansion

The steady-state system is *vertically parametrized*: parameters multiply monomials, $N(\kappa\circ x^M)$. The incidence variety $\{(\kappa, x) : N(\kappa\circ x^M) = 0\}$ is parametrized by $x$ and $w = \kappa\circ x^M \in \ker N$, so it is irreducible of the expected dimension, and the Jacobian at a point depends only on $(w, h = x^{-1})$ through $N\operatorname{diag}(w)M^\top\operatorname{diag}(h)$. If the rank condition holds at one point it holds on a Zariski-dense set, and the projection to parameters is then generically finite and étale onto an open region; if it fails, the Jacobian is singular everywhere and the image has measure zero. ACR is the statement that the projection of the steady-state variety to the $x_i$ axis is finite, read off from the rank of the Jacobian with column $i$ deleted or from elimination.

## Sources

- E. Feliu, O. Henriksson and B. Pascual-Escudero, "The generic geometry of steady state varieties", *SIAM Journal on Applied Algebra and Geometry* 10(3) (2026), 519–548, Theorems A, B and C (proved in Sections 3–5), <https://doi.org/10.1137/25m1731289> (preprint arXiv:2412.17798).
