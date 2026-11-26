# Laplacian form and convergence of detailed-balanced mass-action networks

**Setting.** A chemical reaction network has $m$ species with concentrations $x\in\mathbb R^m_+$, $c$ complexes collected in the complex-stoichiometric matrix $Z\in\mathbb R^{m\times c}$, and $r$ reversible reactions forming a directed complex graph with incidence matrix $B\in\mathbb R^{c\times r}$. The stoichiometric matrix is $S=ZB$ and mass-action kinetics gives $\dot x=Sv(x)$, with $v_j=k^{\rm forw}_j\prod x^{\text{substrate}}-k^{\rm rev}_j\prod x^{\text{product}}$. A *thermodynamic equilibrium* is an $x^*\in\mathbb R^m_+$ with $v(x^*)=0$ (detailed balance). Let $K^{eq}_j=k^{\rm forw}_j/k^{\rm rev}_j$; $\mathrm{Ln}$ and $\mathrm{Exp}$ act componentwise.

**Proposition (existence).** A thermodynamic equilibrium exists iff all forward and reverse rate constants are positive and $\mathrm{Ln}(K^{eq})\in\operatorname{im}S^\top$ (the Wegscheider conditions). The set of all thermodynamic equilibria is then

$$\mathcal E=\{x^{**}\in\mathbb R^m_+: S^\top\mathrm{Ln}(x^{**})=S^\top\mathrm{Ln}(x^*)\}.$$

**Laplacian form.** With balanced reaction constants $\kappa_j(x^*)>0$ and $\mathcal K(x^*)=\mathrm{diag}(\kappa_j(x^*))$, the dynamics is

$$\dot x=-Z\,B\,\mathcal K(x^*)\,B^\top\,\mathrm{Exp}\Bigl(Z^\top\mathrm{Ln}\frac{x}{x^*}\Bigr),$$

where $L=B\mathcal K(x^*)B^\top$ is a symmetric weighted Laplacian of the complex graph. For a connected complex graph, changing the reference equilibrium only rescales $\mathcal K$ by a positive constant.

**Theorem.** For a balanced (detailed-balanced) mass-action network:
1. the set of all equilibria in $\mathbb R^m_+$ equals the set $\mathcal E$ of thermodynamic equilibria;
2. for every positive initial condition, $x(t)$ converges to $\mathcal E$ as $t\to\infty$; within each positive stoichiometric compatibility class there is exactly one equilibrium.

## Expansion

The function $G(x)=x^\top\mathrm{Ln}(x/x^*)+(x^*-x)^\top\mathbf 1$ (Gibbs free energy) has gradient $\mathrm{Ln}(x/x^*)$, and along solutions

$$\dot G=-\gamma^\top L\,\mathrm{Exp}(\gamma),\qquad\gamma=Z^\top\mathrm{Ln}\frac x{x^*},$$

which is $\le0$ because for a symmetric Laplacian $\gamma^\top L\,\mathrm{Exp}(\gamma)=\tfrac12\sum_{\text{edges}}\kappa_{ij}(\gamma_i-\gamma_j)(e^{\gamma_i}-e^{\gamma_j})\ge0$ by monotonicity of the exponential; it vanishes iff $B^\top\gamma=0$, i.e. $S^\top\mathrm{Ln}(x/x^*)=0$. LaSalle's principle then gives convergence to $\mathcal E$. The same structure supports interconnection of networks and Kron-reduction-based model reduction.

## Sources

- Arjan van der Schaft, Shodhan Rao and Bayu Jayawardhana, "On the Mathematical Structure of Balanced Chemical Reaction Networks Governed by Mass Action Kinetics", arXiv:1110.6078 (2011), Section 3 (Propositions 3.2, 3.3 and 3.6, the balanced form) and Section 4 (Theorems 4.1 and 4.2), <https://doi.org/10.48550/arXiv.1110.6078>.
