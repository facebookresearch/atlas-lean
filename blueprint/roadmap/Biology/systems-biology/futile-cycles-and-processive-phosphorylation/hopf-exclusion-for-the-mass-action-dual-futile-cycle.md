# Hopf exclusion for the mass-action dual futile cycle

**Network.** The sequential and distributive dual futile cycle (two-site phosphorylation by a kinase $E$ and dephosphorylation by a phosphatase $F$) is

$$A+E\rightleftharpoons U\to B+E\rightleftharpoons V\to C+E,\qquad C+F\rightleftharpoons X\to B+F\rightleftharpoons Y\to A+F,$$

with substrates $A,B,C$, enzymes $E,F$ and intermediates $U,V,X,Y$; there are three conservation laws (total substrate, total kinase, total phosphatase). Assume each reaction rate is a positive function of its reactant concentrations with positive partial derivatives. At a positive steady state the Jacobian, restricted to a stoichiometric compatibility class, is a $6\times6$ matrix $G_{\mathrm{red}}$ whose entries are built from 16 positive symbols (the partial derivatives of the rates).

**Theorem (parameter-rich kinetics admit Hopf bifurcations).** There are choices of the 16 partial-derivative symbols, for instance all equal to $1$ except $b_{10}=0.01$, $e_4=4\cdot10^4$ and $v_6$ varying in $[5,4\cdot10^4]$, along which $\det G_{\mathrm{red}}<0$ throughout but one real eigenvalue stays positive while a complex pair crosses from the left to the right half-plane. Hence purely imaginary eigenvalues occur at some intermediate $v_6^*$. For parameter-rich kinetics (Michaelis-Menten, generalized mass action) every such symbol choice is realizable at a steady state, so these systems have the capacity for Hopf bifurcation, and by global Hopf theory they have non-stationary periodic orbits for some parameters.

**Theorem (mass action excludes Hopf).** Under mass-action kinetics the symbols are constrained at positive steady states by two equalities,

$$\frac{u_3}{u_2+u_3}\,\frac{b_4}{b_{10}}=\frac{y_{12}}{y_{11}+y_{12}}\,\frac{e_4}{e_1}$$

and an analogous relation for the second phosphorylation step (necessary and sufficient for realizability). Under these constraints $G_{\mathrm{red}}$ never has a pair of non-zero purely imaginary eigenvalues, so the mass-action dual futile cycle has no capacity for Hopf bifurcation at any positive steady state.

## Expansion

Write the characteristic polynomial of $G_{\mathrm{red}}$ with coefficients $\mathfrak c_0,\dots,\mathfrak c_6$ and Hurwitz determinants $\Delta_i$. A purely imaginary pair requires the vanishing of $\Delta_5$, which factors through the identity $\Delta_2\Delta_5=(\mathfrak c_5\Delta_2-\mathfrak c_1^2\mathfrak c_6)\Delta_4-\mathfrak c_6\Delta_3^2$. Structural sign arguments give $\mathfrak c_0,\dots,\mathfrak c_4>0$ and $\Delta_1,\Delta_2,\Delta_3>0$; under mass action, $\Delta_4>0$, and a purely imaginary pair would force $\mathfrak c_6>0$. On the path-connected region $\mathfrak c_6>0$, $\Delta_5>0$ follows if an explicit combination $\mathcal T=P_5\Delta_4-P_6B_1^+-N_5B_2^+$ is non-negative. Rewriting $\mathcal T$ in mass-action steady-state coordinates and clearing positive denominators gives a large polynomial $\widetilde{\mathcal T}^*$; a positivity certificate (grouping its terms into manifestly positive blocks) shows $\widetilde{\mathcal T}^*>0$, so $\mathcal T>0$, $\Delta_5\ne0$, and no eigenvalue pair can cross the imaginary axis. The contrast shows that oscillations in this motif depend on kinetic detail: the network structure alone allows them, mass action does not. The positivity certificate was found with computer assistance and verified symbolically.

## Sources

- N. Vassena, "Sequential and distributive dual futile cycle: Hopf bifurcation can occur under parameter-rich kinetics but cannot occur under mass action kinetics", arXiv:2608.27081 (2026), Section 3 (explicit example), Section 4 (Propositions 4.1-4.2, Lemmas 4.3-4.4, Corollary 4.5), Section 5 (Proposition 5.1, Lemma 5.3, Proposition 5.4, Proposition 5.6, Lemma 5.7, Theorem 5.8), <https://doi.org/10.48550/arXiv.2608.27081>.
