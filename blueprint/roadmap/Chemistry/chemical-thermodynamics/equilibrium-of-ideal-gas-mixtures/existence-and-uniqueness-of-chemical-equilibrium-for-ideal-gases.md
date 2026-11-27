# Existence and uniqueness of chemical equilibrium for an ideal-gas mixture

This node covers the Gibbs-minimization characterization of chemical equilibrium. Consider $N$ ideal-gas species at fixed temperature
$T > 0$ and pressure $p > 0$, with standard chemical potentials $\mu_i^\circ(T)$, element-composition matrix $A$ (entry $A_{ki}$ is the number of
atoms of element $k$ in species $i$, every species containing at least one atom) and element totals $b = A n^0$ for some $n^0 \ge 0$. The Gibbs energy

$$G(n) = \sum_{i=1}^N n_i\Big(\mu_i^\circ(T) + RT\ln\frac{n_i\,p}{n_{\mathrm{tot}}\,p^\circ}\Big), \qquad n_{\mathrm{tot}} = \sum_i n_i,$$

extended by continuity where some $n_i = 0$, attains its minimum on the polytope $\{n \ge 0 : An = b\}$. If this polytope contains a point
with all $n_i > 0$, the minimizer is unique and strictly positive, and it is characterized by $\mu_i^\circ(T) + RT\ln(n_i p/(n_{\mathrm{tot}}p^\circ)) = \sum_k \lambda_k A_{ki}$
for some multipliers $\lambda$, the law of mass action in element-potential form.

## Expansion

A good expansion proves existence by compactness and continuity, positivity of the minimizer from the infinite slope of
$x\ln x$ at zero, and uniqueness from strict convexity of $G$ on the relevant face once the scale invariance along $n \mapsto tn$ is removed by
the element constraints. Coupling the equilibrium composition to an adiabatic energy balance is a separate node.

## Sources

- M. J. Moran and H. N. Shapiro, *Fundamentals of Engineering Thermodynamics*, 6th edition, Wiley, 2008, for chemical equilibrium and the equilibrium constant.
