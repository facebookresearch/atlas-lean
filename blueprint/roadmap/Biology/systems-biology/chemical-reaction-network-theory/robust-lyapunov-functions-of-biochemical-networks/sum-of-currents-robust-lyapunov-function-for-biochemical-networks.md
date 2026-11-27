# Sum-of-currents robust Lyapunov function for biochemical interaction networks

**Setting.** A biochemical interaction network (BIN) has species $X_1,\dots,X_n$, reactions $\mathcal R_1,\dots,\mathcal R_\nu$ and stoichiometry matrix $\Gamma \in \mathbb R^{n\times\nu}$. Its dynamics are

$$\dot x = \Gamma R(x), \qquad x \in \mathbb R^n_{\ge 0},$$

where the rates are only assumed to be **admissible**: each $R_j$ is $C^1$, vanishes when one of its reactants is absent, and is non-decreasing in each reactant (strictly increasing on the positive orthant), and independent of non-reactants. No functional form (mass action, Michaelis–Menten, Hill, ...) is fixed. A locally Lipschitz $V : \mathbb R^n \to \mathbb R_{\ge 0}$ is a **robust Lyapunov function (RLF)** if $V(x) = 0 \iff \Gamma R(x) = 0$, and its Dini derivative along trajectories is $\le 0$ for every admissible rate vector $R$.

A BIN is **linear** (monomolecular) if each reaction is $X_i \to X_j$, $\emptyset \to X_i$ (constant inflow $u_i \ge 0$) or $X_i \to \emptyset$, with arbitrary strictly increasing $C^1$ rate functions $R_{ij}, R_i$ vanishing at $0$.

**Theorem.**

1. (Linear networks.) For every linear BIN and every admissible choice of rates, the **sum-of-currents** function

$$V(x) = \|\dot x\|_1 = \sum_{i=1}^n \Bigl|\, \sum_{j\ne i}\bigl(R_{ji}(x_j) - R_{ij}(x_i)\bigr) + u_i - R_i(x_i) \Bigr|$$

is an RLF.

2. (Stability-preserving graph modifications.) Let $\tilde{\mathcal N}$ be obtained from a linear BIN by a finite sequence of elementary modifications: reversing a reaction, inserting an intermediate complex, external or conserved regulation of a species, adding a catalyst, or adding a dimer. Then $V = \sum_i |\dot x_i|$, summed over all species of $\tilde{\mathcal N}$, is still an RLF. In particular, replacing each $X_i \to X_j$ by the enzymatic mechanism $X_i + E_{ij} \rightleftharpoons C_{ij} \to X_j + E_{ij}$ keeps $V = \sum_i |\dot x_i| + \sum |\dot c_{ij}|$ an RLF, although the network is now nonlinear.

3. (Consequences.) If such a network also satisfies LaSalle's invariance principle (which holds for the networks in item 2), every bounded trajectory converges to the steady-state set. If moreover a steady state is isolated in its stoichiometric class and all trajectories are bounded, that steady state is globally asymptotically stable in its class, for all admissible kinetics at once.

## Expansion

For a linear network, $\dot x$ itself satisfies the linear time-varying system $\ddot x = J(t)\dot x$, where $J = \Gamma\,\partial R/\partial x$ is a compartmental (Metzler, column-diagonally-dominant) matrix whatever the admissible rates. The $\ell^1$ norm is non-increasing under compartmental flows, so $\|\dot x\|_1$ cannot grow. The modifications in item 2 preserve the needed sign and column-sum structure of the Jacobian in the enlarged state space, which the paper verifies one modification at a time. This gives graphical certificates that replace linear-programming searches for piecewise-linear RLFs.

## Sources

- M. Ali Al-Radhawi, "Graphical characterizations of robust stability in biological interaction networks", arXiv (2023). Section 2 (admissible kinetics AK1–AK3, definition of RLF), Theorem 1, Theorems 3–4 and Corollary 5, Theorem 9, Theorem 10. <https://doi.org/10.48550/arXiv.2302.05090>. Published version: Mathematics of Control, Signals, and Systems 35(3) (2023), 585–617, <https://doi.org/10.1007/s00498-023-00350-9>; locators above refer to the arXiv version.
