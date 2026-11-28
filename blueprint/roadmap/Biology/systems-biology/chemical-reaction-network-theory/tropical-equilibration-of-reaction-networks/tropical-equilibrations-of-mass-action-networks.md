# Tropical equilibrations of mass-action networks

**Setting.** Consider mass-action kinetics with reactions $\sum_i \alpha_{ji} A_i \to \sum_k \beta_{jk} A_k$ and rates $R_j(\mathbf{x}) = k_j \mathbf{x}^{\boldsymbol\alpha_j}$, so that $\dot{\mathbf{x}} = \sum_j k_j (\boldsymbol\beta_j - \boldsymbol\alpha_j)\mathbf{x}^{\boldsymbol\alpha_j}$. Suppose rate constants are powers of a small parameter, $k_j = \bar k_j \epsilon^{\gamma_j}$, and rescale concentrations $x_i = \epsilon^{a_i}\bar x_i$. In the $i$-th equation the reaction $j$ then has order $\epsilon^{\mu_j}$ with

$$
\mu_j = \gamma_j + \langle \mathbf{a}, \boldsymbol\alpha_j \rangle .
$$

**Definition (equilibration).** Reactions $j \ne j'$ are *equilibrated on species $i$* at the exponent vector $\mathbf{a}$ if (i) $\mu_j = \mu_{j'}$; (ii) they act on $i$ with opposite signs, $(\boldsymbol\beta_j - \boldsymbol\alpha_j)_i (\boldsymbol\beta_{j'} - \boldsymbol\alpha_{j'})_i < 0$; and (iii) $\mu_k \ge \mu_j$ for every other reaction $k$ that changes species $i$. A *tropical equilibration* is an $\mathbf{a}$ at which every species is equilibrated.

**Results.**
1. *(Geometry.)* For each species $i$ let $f_i(\mathbf{a}) = \min_j (\gamma_j + \langle \mathbf{a}, \boldsymbol\alpha_j\rangle)$ over reactions changing $i$. The non-linearity locus of the min-plus polynomial $f_i$ (where the minimum is attained at least twice) is in bijection with the tropical hypersurface of the right-hand side $P_i(\mathbf{x})$; tropical equilibrations are the points of the intersection of these loci over all $i$ at which the two minimizing monomials have opposite signs.
2. *(Necessity.)* If a tropically truncated system (keeping only dominant monomials in each equation) is permanent, then each of its equations has at least two terms, one production and one degradation term; this is why equilibrated pairs of opposite sign are required.
3. *(Approximation.)* If the full system is permanent, the solutions $x$ of the full system and $\hat x$ of its complete or two-term tropicalization (each right-hand side replaced by its dominant monomials) from the same initial data satisfy $|x(t) - \hat x(t)| < C_1 \epsilon^{\gamma} e^{bt}$ for some $\gamma > 0$ and constants $C_1, b$.

## Proof sketch

When rates and concentrations live on well-separated scales, each species' equation is dominated by its few largest monomials, and replacing sums by maxima turns logarithms of concentrations into a piecewise-linear (tropical) problem. A slow, quasi-steady regime for species $i$ needs a dominant production term balanced by a dominant degradation term of the same order; otherwise the species would grow or decay at the leading-order rate. The equilibration conditions are therefore the leading-order balance conditions, and solving them by linear algebra on the exponents $\mathbf{a}$ yields the orders of magnitude of concentrations without solving the ODE, which is the basis of tropical model reduction.

## Related topics

- [Chemical reaction network theory](../README.md)

## Sources

- Vincent Noel, Dima Grigoriev, Sergei Vakulenko and Ovidiu Radulescu, "Tropicalization and tropical equilibration of chemical reactions", in *Contemporary Mathematics*, American Mathematical Society, 2014, 261–275, <https://doi.org/10.1090/conm/616/12316>. Preprint version: arXiv:1303.3963 (2013), Section 3 (Proposition 3.2, Lemma 3.3), Section 4 (Definition of equilibrated reactions, Proposition 4.2), <https://doi.org/10.48550/arXiv.1303.3963>.
