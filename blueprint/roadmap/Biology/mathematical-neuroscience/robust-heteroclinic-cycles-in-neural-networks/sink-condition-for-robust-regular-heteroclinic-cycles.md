# Sink condition for robust regular heteroclinic cycles

Use the setting of [robustness under invariant-subspace constraints](robustness-of-heteroclinic-cycles-under-invariant-subspace-constraints.md): $f \in X_{\mathcal{I}}$ leaves invariant every subspace of an intersection-closed family $\mathcal{I}$, and a heteroclinic cycle $\Sigma$ joins $x_1, \dots, x_p$ with $I_{c(i)}$ the smallest element of $\mathcal{I}$ containing the connection $s_i$.

A heteroclinic cycle is **regular** if it consists of hyperbolic equilibria and connections $s_i \subset W^u(x_i)$ with $W^u(x_i) \subset W^s(x_{i+1})$ for every $i$.

**Theorem (equilibria).** Let $\Sigma$ be a regular heteroclinic cycle of $f \in X_{\mathcal{I}}$ between hyperbolic equilibria. If for every $i$ the next equilibrium is a sink for the dynamics restricted to the connecting subspace,

$$\dim\big(W^s(x_{i+1}) \cap I_{c(i)}\big) = \dim I_{c(i)},$$

then $\Sigma$ is robust to perturbations in $X_{\mathcal{I}}$.

**Theorem (equilibria or periodic orbits).** Let $\Sigma$ be a heteroclinic cycle of $f \in X_{\mathcal{I}}$ between hyperbolic equilibria or hyperbolic periodic orbits $x_1, \dots, x_p$ that contains all their unstable manifolds, with $S_i$ the manifold of connections from $x_i$ to $x_{i+1}$. If there are $I_{c(1)}, \dots, I_{c(p)} \in \mathcal{I}$ with $I_{c(i)} \supseteq S_i$ and $\dim(W^s(x_{i+1}) \cap I_{c(i)}) = \dim I_{c(i)}$ for all $i$, then $\Sigma$ is robust to perturbations within $X_{\mathcal{I}}$.

## Expansion

If $x_{i+1}$ attracts a full neighbourhood of itself inside the invariant subspace $I_{c(i)}$, then any orbit in $I_{c(i)}$ leaving $x_i$ and entering that neighbourhood converges to $x_{i+1}$, and this persists under small perturbations that keep $I_{c(i)}$ invariant; transversality inside $I_{c(i)}$ holds automatically, so no unfolding perturbation is needed. The second theorem extends the argument to connections between periodic orbits, which matters for networks of spiking neurons where no phase reduction to equilibria is available: there $\dim W^u(p) + \dim W^s(p) = n+1$ for a hyperbolic periodic orbit, and the coupling structure alone can force robust cycles, as in a four-cell Hodgkin–Huxley-type network.

## Depends on

- [Robustness of heteroclinic cycles under invariant-subspace constraints](robustness-of-heteroclinic-cycles-under-invariant-subspace-constraints.md)

## Sources

- P. Ashwin, Ö. Karabacak, T. Nowotny, "Criteria for robustness of heteroclinic cycles in neural microcircuits", Journal of Mathematical Neuroscience 1 (2011) 13, Section 2 (Equations 2–3, Proposition 1, Equations 6–8, Theorem 1) and Section 2.1–2.3 (Theorems 2 and 3), <https://doi.org/10.1186/2190-8567-1-13>, PMCID PMC3365877.
