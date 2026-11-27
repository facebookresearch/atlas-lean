# Persistent reactions of a reaction-diffusion system form a SOR

**Setting.** Let $(\mathcal{S}, \mathcal{R})$ be a reaction network with $n$ species, $m$ reactions and stoichiometric matrix $N$, and consider a reaction-diffusion system for concentrations $c(x,t) \in \mathbb{R}^n_+$ of the form

$$\partial_t c_i = d_i \,\Delta c_i + \bigl(N\, v(c)\bigr)_i, \qquad i = 1,\dots,n,$$

on a connected domain $\Omega$ with $C^2$ boundary and $0 < |\Omega| < \infty$, with nonnegative initial data $c_i(x,0) = c_i^0(x) \ge 0$ and homogeneous Neumann boundary conditions $\partial c_i/\partial\nu = 0$ on $\partial\Omega$ for $i = 1,\dots,n$ (the source's system (23)), where

- the diffusion rates satisfy $d_i \ge 0$;
- the flux function $v : \mathbb{R}^n_+ \to \mathbb{R}^m_+$ is Lipschitz on bounded sets and **feasible**: for every $c$, $v(c)_r > 0$ iff every species in $\operatorname{supp}(r)$ is present ($c_s > 0$).

Let $\hat c$ be a solution with $\partial_t \hat c$ and the second spatial derivatives continuous in $(x,t)$, and $|\hat c(x,t)| < K$ for all $x \in \Omega$, $t \ge 0$.

**Theorem 4.** The set of persistent species of $\hat c$ is a distributed organization, through a flux $\hat v \in \mathbb{R}^m_+$ obtained by integrating $v(\hat c(x,t))$ over space and time, and the set of persistent reactions

$$\{ r \in \mathcal{R} : \hat v_r > 0 \}$$

is a set of organizational reactions. A reaction persists iff all species in its support persist.

**Consequences.** (i) A set of reactions that is not a SOR cannot be the persistent reaction set of any bounded solution of any such system on the network; it can only be transient. (ii) Right after the initial time, each compartment activates the elementary reaction closure of its initially active reactions, so the persistent reactions are always contained in the union of the ERCs of the initially active reactions. (iii) Enumerating all SORs, which needs only the network, therefore lists every possible long-term set of active reactions ("persistent subspace") independently of kinetic laws and rate constants. The same statement holds for the ODE and patch (compartment) special cases.

## Expansion

The species-level theorem (persistent species form a DO) comes from averaging the dynamics: species that persist must be produced at least as fast as consumed on average, giving $N\hat v \ge 0$ for the time- and space-integrated flux, and the spatial regions where different subsets coexist play the role of compartments, each closed under its own reactions. Feasibility of $v$ ties reaction activity to species presence, so the support of $\hat v$ is exactly the set of reactions supported by persistent species, which is the SOR of that DO.

## Depends on

- [SOR characterization by elementary reaction closures](sor-characterization-by-elementary-reaction-closures.md)

## Sources

- S. Peter, L. Woitke, P. Dittrich, B. Ibrahim, "Computing all persistent subspaces of a reaction-diffusion system", Scientific Reports 13 (2023) 17169, system (23), Theorem 4 and the discussion following it (other boundary conditions need extra reactions in the network), <https://doi.org/10.1038/s41598-023-44244-x>, PMCID PMC10567720.
