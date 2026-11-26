# Absolute concentration robustness in complex balanced systems

**Setting.** Let $(\mathcal{G},K)$ be a complex balanced mass-action system with species $X_1,\dots,X_n$, stoichiometric subspace $\mathcal{S}\subseteq\mathbb{R}^n$, and standard basis vectors $e_i$. Static ACR and the dynamic ACR basin types are defined in the dependency.

**Theorem.** The following are equivalent:
- (A1) $x_i$ is a static ACR variable;
- (A2) $e_i\in\mathcal{S}$;
- (A3) there are reactions $y_1\to y_1',\dots,y_m\to y_m'$ in $\mathcal{G}$ and integers $\lambda_j$ with $\sum_j\lambda_j(y_j'-y_j)=\alpha X_i$ for some nonzero integer $\alpha$.

The following are also equivalent:
- (B1) $x_i$ is a dynamic ACR variable;
- (B2) $x_i$ is a wide basin dynamic ACR variable;
- (B3) $x_i$ is a full basin dynamic ACR variable.

Each (B) statement implies each (A) statement. If the positive steady states of $(\mathcal{G},K)$ are globally attracting within their compatibility classes, all six statements are equivalent. This holds, for example, when $\mathcal{G}$ is connected or $\dim\mathcal{S}\le3$, and it holds in general if the Global Attractor Conjecture is true.

**Corollaries.**
- In a complex balanced system, if two complexes in the same linkage class differ only in $X_i$, then $x_i$ is static ACR. This applies in particular if $0\to X_i$ or $X_i\to0$ is a reaction.
- For a weakly reversible deficiency-zero network, the equivalences hold for every choice of rate constants.
- A mass-conserving complex balanced system is neither static nor dynamic ACR. Hence a weakly reversible, deficiency-zero, mass-conserving network has no capacity for either kind of ACR.

## Depends on

- [Static and dynamic absolute concentration robustness](static-and-dynamic-absolute-concentration-robustness.md)
- [Complex balancing and the deficiency zero theorem](../complex-balancing-and-the-deficiency-zero-theore/README.md)

## Expansion

By Horn–Jackson, the positive steady states of a complex balanced system form the log-linear set $\log Z=\log\tilde{x}+\mathcal{S}^\perp$ through any complex balanced equilibrium $\tilde{x}$. Static ACR in $x_i$ says $\log Z$ lies in a hyperplane $\{y_i=\text{const}\}$. That is equivalent to $\mathcal{S}^\perp\subseteq\{y_i=0\}$, and so to $e_i\in\mathcal{S}$. Statement (A3) restates (A2) in terms of integer combinations of reaction vectors. For the (B) statements, dynamic ACR implies static ACR, so $e_i\in\mathcal{S}$. Every positive point is then compatible with every hyperplane $\{x_i=c\}$, so convergence holds from all positive initial data, which is full basin. Under global attraction, $e_i\in\mathcal{S}$ means every compatibility class contains exactly one positive steady state, with the same $i$-th coordinate. All trajectories therefore converge to that value. A positive conservation law $w$ with full support would give $w\perp e_i$, impossible since $w_i>0$. So mass conservation excludes (A2), and with it all six properties.

## Sources

- B. Joshi, G. Craciun, "Foundations of static and dynamic absolute concentration robustness", arXiv preprint (2021): Theorem 6.1, Corollaries 6.2, 6.3, 6.5 and 6.6, and Remark 6.4 (Section 6, ACR in complex balanced systems). <https://doi.org/10.48550/arXiv.2104.14070>
