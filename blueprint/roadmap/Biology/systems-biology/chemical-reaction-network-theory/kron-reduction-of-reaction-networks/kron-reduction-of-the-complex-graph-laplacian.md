# Kron reduction of the complex-graph Laplacian

**Setting.** A chemical reaction network with $c$ complexes, $m$ species, complex stoichiometric matrix $Z \in \mathbb N^{m\times c}$ and complex-graph incidence matrix $B$ can be written, under enzyme kinetics in which each reaction rate has the form $v_j(x) = d_j(x)k_j\exp(Z_{S_j}^\top\mathrm{Ln}\,x)$ ($d_j$ rational, $d_j \equiv 1$ for mass action, $Z_{S_j}$ the substrate complex), as

$$\dot x = -Z\,L(x)\,\mathrm{Exp}\big(Z^\top\mathrm{Ln}\,x\big),$$

with a weighted Laplacian $L(x) \in \mathbb R^{c\times c}$ of the complex graph: nonnegative diagonal (zero exactly at complexes with no outgoing reaction), nonpositive off-diagonal entries and zero column sums, $\mathbb 1_c^\top L(x) = 0$.

**Proposition (Schur complement).** Let $\mathcal V_r$ be a set of complexes such that from every complex in $\mathcal V_r$ there is a directed path in the complex graph to a complex outside $\mathcal V_r$ (so that $L_{22}(x)$ below is invertible). Partition $L(x)$ into blocks with $L_{22}(x)$ indexed by $\mathcal V_r$ and set

$$\hat L(x) = L_{11}(x) - L_{12}(x)L_{22}(x)^{-1}L_{21}(x).$$

Then $\hat L(x)$ is again a weighted Laplacian on the remaining $\hat c = c - |\mathcal V_r|$ complexes: its diagonal entries are nonnegative, its off-diagonal entries have the Laplacian sign, and $\mathbb 1_{\hat c}^\top\hat L(x) = 0$ for every $x \in \mathbb R^m_+$.

**Reduction method.** Replacing $L(x)$ by $\hat L(x)$ and $Z$ by its columns for retained complexes yields a reduced network $\dot x = -\hat Z\hat L(x)\mathrm{Exp}(\hat Z^\top\mathrm{Ln}\,x)$ of the same form (a **Kron reduction**, as for resistive electrical networks), which keeps the form of a reaction network governed by enzyme kinetics on fewer complexes and approximates the transient behaviour of the retained metabolites.

## Proof sketch

Zero column sums pass to the Schur complement because $\mathbb 1^\top L = 0$ gives $\mathbb 1^\top L_{11} = -\mathbb 1^\top L_{21}$ and $\mathbb 1^\top L_{12} = -\mathbb 1^\top L_{22}$, so $\mathbb 1^\top\hat L = -\mathbb 1^\top L_{21} + \mathbb 1^\top L_{22}L_{22}^{-1}L_{21} = 0$; the sign pattern follows because $L_{22}^{-1}$ is entrywise nonnegative for an invertible M-matrix. The path condition is what makes $L_{22}$ invertible: for the single reaction $A \to B$, $L = \begin{pmatrix}k & 0\\ -k & 0\end{pmatrix}$, and with $\mathcal V_r = \{B\}$ the block $L_{22} = 0$ is singular. Eliminating complexes reroutes the flows through them as direct reactions between their neighbours in the complex graph, exactly as Kron reduction replaces internal nodes of a resistor network by equivalent resistances between boundary nodes. In a yeast glycolysis model the reduction reproduces the transients of key metabolites with fewer equations.

## Sources

- Shodhan Rao, Arjan van der Schaft, Karen van Eunen, Barbara M. Bakker and Bayu Jayawardhana, "Model-order reduction of biochemical reaction networks", in *2013 European Control Conference (ECC)*, IEEE, 2013, 4502–4507, <https://doi.org/10.23919/ecc.2013.6669587>. Preprint version: arXiv:1212.2438 (2012), Section 3 (dynamics under enzyme kinetics) and Proposition 4.1 (Section 4), <https://doi.org/10.48550/arXiv.1212.2438>.
