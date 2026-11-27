# Injectivity of a closed reaction network from its fully open extension

Let $\mathcal{N}$ be a chemical reaction network with $n$ species, stoichiometric subspace $\Gamma = \langle y' - y : y \to y' \rangle \subseteq \mathbb{R}^n$ of dimension $s$, and mass-action species formation rate $f_\kappa(c) = \sum_{y\to y'} k_{y\to y'}\, c^{y}\,(y' - y)$ for rate vectors $\kappa \in \mathbb{R}_{>0}^{\mathcal{R}}$. The network is **injective** if for every $\kappa$ and all distinct $a, b \in \mathbb{R}^n_{>0}$ with $a - b \in \Gamma$ one has $f_\kappa(a) \ne f_\kappa(b)$; then each stoichiometric class contains at most one positive steady state for every choice of rate constants.

**Jacobian characterization.** $\mathcal{N}$ is injective if and only if $\ker J_c(f_\kappa) \cap \Gamma = \{0\}$ for all $c \in \mathbb{R}^n_{>0}$ and all $\kappa$. Consequently an injective network has no degenerate positive steady states.

**Closed networks.** Call $\mathcal{N}$ closed if $\Gamma \ne \mathbb{R}^n$, let $d = n - s$, and let $\mathcal{N}^o$ be the **fully open network** obtained by adding an outflow reaction $S_i \to 0$ for every species lacking one, with species formation rate $g_{\kappa^o}$, where all added outflow rate constants equal $1$. Suppose $\mathcal{N}^o$ is injective. Then the following are equivalent:

1. $\mathcal{N}$ is injective;
2. as a polynomial in $\kappa$, $\det J_c(g_{\kappa^o})$ has at least one monomial of total degree $s$;
3. $\ker J_c(f_\kappa) \cap \Gamma = \{0\}$ for **some** single $\kappa$ and $c \in \mathbb{R}^n_{>0}$;
4. there are a set $I$ of $d$ species indices carrying added outflows and $s$ reactions $y^i \to y'^i$ of the projected network $\mathcal{N}_I$ such that both $\{y^i - y'^i\}_{i \le s}$ and $\{y^i\}_{i \le s}$ are linearly independent.

When these hold, all steady states of $\mathcal{N}$ are non-degenerate.

## Depends on

- [Mass-action reaction rate](../../complex-balancing-and-the-deficiency-zero-theore/rate.md)

## Expansion

If $f_\kappa(a) = f_\kappa(b)$ with $a - b = \gamma \in \Gamma$, take the logarithmic means $c_i = (a_i - b_i)/\log(a_i/b_i)$; then $a^y - b^y$ has the sign of $y \ast_c \gamma$, and rescaling rate constants converts the difference into a Jacobian kernel vector, and conversely. For a closed network, replacing $d$ rows of the Jacobian by a reduced basis of conservation laws gives an extended Jacobian whose determinant is the degree-$s$ part of $(-1)^d \det J_c(g_{\kappa^o})$. Injectivity of $\mathcal{N}^o$ forces all coefficients of that polynomial to share a sign, so the degree-$s$ part is either identically zero or never zero, which gives the equivalences. The two-site modification cycle fails the criterion, consistent with its known multistationarity.

## Sources

- Elisenda Feliu and Carsten Wiuf, "Preclusion of switch behavior in networks with mass-action kinetics", Applied Mathematics and Computation 219 (2012), 1449–1467, <https://doi.org/10.1016/j.amc.2012.07.048>; numbering as in arXiv:1109.5149: Section 5 (Jacobian characterization of injectivity) and Theorem 9.1 with Corollary 9.2.
