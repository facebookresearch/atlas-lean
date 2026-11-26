# Robustness of heteroclinic cycles under invariant-subspace constraints

Let $X$ be the set of $C^1$ vector fields on $\mathbb{R}^n$ with bounded global attractors and consider $\dot x = f(x)$, $f \in X$. A **heteroclinic cycle** $\Sigma$ is an invariant set consisting of hyperbolic equilibria $x_1, \dots, x_p$ ($x_{p+1} = x_1$) and connecting orbits $s_i \subset W^u(x_i) \cap W^s(x_{i+1})$. $\Sigma$ is **robust to perturbations in** $Y \subseteq X$ if $f \in Y$ and every $g \in Y$ in some $C^1$-neighbourhood of $f$ has a heteroclinic cycle close to $\Sigma$.

**Proposition (no robustness without constraints).** A heteroclinic cycle between $p \ge 1$ hyperbolic equilibria is never robust to general $C^1$ perturbations in $X$.

**Constrained setting.** Let $\mathcal{I} = \{I_1, \dots, I_d\}$ be a finite family of nonempty affine subspaces of $\mathbb{R}^n$, closed under nonempty intersection and containing $I_1 = \mathbb{R}^n$, and let $X_{\mathcal{I}} = \{ f \in X : f(I_j) \subseteq T I_j \text{ for all } j \}$ be the vector fields leaving every $I_j$ invariant (for example fixed-point subspaces of a symmetry group, or synchrony subspaces of a coupled cell network). For a cycle of $f \in X_{\mathcal{I}}$ let $I_{c(i)}$ be the smallest element of $\mathcal{I}$ containing $s_i$; the sequence $x_1 \xrightarrow{I_{c(1)}} x_2 \to \cdots \xrightarrow{I_{c(p)}} x_1$ is the connection scheme.

**Theorem.** Let $\Sigma$ be a heteroclinic cycle of $f \in X_{\mathcal{I}}$ between hyperbolic equilibria with this connection scheme.

1. If $\Sigma$ is robust to perturbations in $X_{\mathcal{I}}$ (preserving the connection scheme), then for every $i$

$$\dim\big(W^u(x_i) \cap I_{c(i)}\big) + \dim\big(W^s(x_{i+1}) \cap I_{c(i)}\big) \ge \dim I_{c(i)} + 1. \qquad (*)$$

2. Conversely, if $(*)$ holds for every $i$, there is $\tilde f \in X_{\mathcal{I}}$ arbitrarily close to $f$ for which $\Sigma$ is a heteroclinic cycle robust to perturbations in $X_{\mathcal{I}}$.

## Expansion

For general perturbations a connection persists only if $W^u(x_i)$ and $W^s(x_{i+1})$ meet transversally, which needs $\dim W^u(x_i) + \dim W^s(x_{i+1}) \ge n+1$. Since $\dim W^u(x_i) + \dim W^s(x_i) = n$ at every hyperbolic equilibrium, summing over the cycle gives exactly $pn$, so the $p$ transversality inequalities cannot all hold; this is the proposition, a special case of the Kupka–Smale theorem. Inside $X_{\mathcal{I}}$, each connection lives in the invariant subspace $I_{c(i)}$, and near a typical point of $s_i$ perturbations within $X_{\mathcal{I}}$ are unconstrained inside $I_{c(i)}$, so the transversality count is made relative to $I_{c(i)}$. A perturbation may be needed to put a tangential intersection in general position, which is why the converse is stated for a nearby $\tilde f$. The result explains winnerless-competition heteroclinic cycles in Lotka–Volterra and coupled-neuron models: the observed cycle of a three-cell inhibitory microcircuit is not robust to perturbations that only preserve its $\mathbb{Z}_3$ symmetry, but is robust once the invariant subspaces forced by the coupling are respected.

## Sources

- P. Ashwin, Ö. Karabacak, T. Nowotny, "Criteria for robustness of heteroclinic cycles in neural microcircuits", Journal of Mathematical Neuroscience 1 (2011) 13, Section 2 (Equations 2–3, Proposition 1, Equations 6–8, Theorem 1) and Section 2.1–2.3 (Theorems 2 and 3), <https://doi.org/10.1186/2190-8567-1-13>, PMCID PMC3365877.
