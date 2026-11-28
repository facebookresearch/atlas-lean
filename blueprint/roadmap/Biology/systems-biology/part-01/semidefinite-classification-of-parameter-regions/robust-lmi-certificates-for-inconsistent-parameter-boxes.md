# Robust LMI certificates for inconsistent parameter boxes

**Lemma (robust linear matrix inequality).** Let $A_0, A_1, \dots, A_n$ be symmetric matrices. If there exist $\eta > 0$ and symmetric matrices $W_1, \dots, W_n$ with

$$A_0 = \sum_{i=1}^n W_i, \qquad W_i + \eta A_i \succeq 0, \qquad W_i - \eta A_i \succeq 0 \qquad (i = 1, \dots, n),$$

then

$$A_0 + \sum_{i=1}^n \delta_i A_i \succeq 0 \qquad \text{for all } \delta \text{ with } |\delta_i| \le \eta.$$

For fixed $A_0, \dots, A_n$ the conditions are affine in $(\eta, W_1, \dots, W_n)$, so the largest certified $\eta$ is found by one semidefinite program.

**Application to parameter regions.** In the semidefinite relaxation of steady-state data consistency, only the matrices $Q_i$ depend on the rate constants, and affinely. Around a nominal point $k^0$ with half-widths $\Delta k_j$, write $\delta_j = (k_j - k_j^0)/\Delta k_j$ and

$$Q_i(k) = Q_i^0 + \sum_j Q_{ij}\, \delta_j\, \Delta k_j .$$

Fix dual multipliers $(\gamma, \lambda, r, S)$ with $\gamma > 0$ that certify infeasibility at $k^0$. The dual matrix inequality is then an LMI of the form $A_0 + \sum_j \delta_j A_j \succeq 0$, and the Lemma yields a factor $\eta$ such that the same multipliers remain dual feasible on the whole box $|k_j - k_j^0| \le \eta\, \Delta k_j$. Every parameter vector in that box is therefore inconsistent with the steady-state data.

## Expansion

The Lemma follows from the identity

$$A_0 + \sum_{i=1}^n \delta_i A_i = \frac{1}{2\eta} \sum_{i=1}^n \Bigl[(\eta + \delta_i)(W_i + \eta A_i) + (\eta - \delta_i)(W_i - \eta A_i)\Bigr],$$

whose right side is a sum of positive semidefinite matrices with nonnegative coefficients whenever $|\delta_i| \le \eta$. Equivalently, the inequality holds at every vertex of the box, and positive semidefiniteness of an affine family is preserved on the convex hull; the same idea extends to any polyhedral partition, for example simplices.

The classification algorithm repeatedly picks an unexplored parameter point, solves the dual problem there, and, if a certificate exists, grows the surrounding box while dual feasibility holds, then removes the box from the search space and adds it to the inconsistent set. Unlike grid sampling, a single small SDP discards a full-dimensional region, and no feasible parameter can be missed by falling between grid points. Certified boxes grow with distance from the feasible region, so the maximal perturbation $\eta$ also indicates promising search directions. When no parameter of a candidate mechanism survives, the model structure is rejected; in a branched enzymatic pathway this discriminates whether a metabolite cooperatively activates one conversion, since the model without that effect requires an implausibly large measurement tolerance to fit the data.

## Depends on

- [Semidefinite relaxation for steady-state data consistency](semidefinite-relaxation-for-steady-state-data-consistency.md)

## Sources

- L. Kuepfer, U. Sauer, P. A. Parrilo, "Efficient classification of complete parameter regions based on semidefinite programming", BMC Bioinformatics 8 (2007) 12, Appendix, "Proof for regions of inconsistency" (Lemma 1, Equations 21 and 22 and the proof identity), Table 1 (classification algorithm), Figures 1 and 2 (certified boxes and maximal perturbation), Table 2 and Figures 3 and 4 (model discrimination), <https://doi.org/10.1186/1471-2105-8-12>, PMCID PMC1800867.
