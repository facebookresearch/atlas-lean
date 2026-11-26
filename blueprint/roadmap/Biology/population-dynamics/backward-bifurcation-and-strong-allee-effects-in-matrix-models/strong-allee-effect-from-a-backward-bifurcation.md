# Strong Allee effect from a backward bifurcation

**Definition.** A population model has a **strong Allee effect** if it has both an extinction attractor and a positive attractor; typically the extinction equilibrium and a positive equilibrium are both stable.

**Setting.** The nonlinear matrix model $x' = rP(x)x$ with $\rho[P(0)] = 1$ under assumption A1 of the fundamental bifurcation theorem, with direction coefficient $\kappa$ and unbounded continuum $\mathcal C^+$ of positive equilibrium pairs from $(1,0)$. Further assume
- (A2) $\kappa < 0$ (backward bifurcation);
- (A3) (a) $\mathcal C^+$ contains a positive equilibrium $x^*$ at $r = 1$, and (b) $x^*$ is locally asymptotically stable by linearization, $\rho[J(x^*)] < 1$.

**Theorem.** Under A1–A3 the model has a strong Allee effect for all $r$ in an interval $(1-\delta, 1)$: the extinction equilibrium is stable (because $r < 1$) and a stable positive equilibrium near $x^*$ coexists with it, separated by the unstable positive equilibria of the backward branch.

**Corollary.** Suppose (A4) there is a function $m(r)$, bounded on bounded subintervals of $[1,\infty)$, with $|x| \le m(r)$ for every equilibrium pair $(r,x) \in \mathcal C^+$. Then the spectrum $\Sigma_r = \{r : (r,x) \in \mathcal C^+\}$ is unbounded, hence an interval $[r_{\min},\infty)$ or $(r_{\min},\infty)$; with A2, $r_{\min} < 1$ and A3(a) holds. The same statements hold with $R_0$ in place of $r$.

## Depends on

- [Fundamental bifurcation theorem for nonlinear matrix models](fundamental-bifurcation-theorem-for-nonlinear-matrix-models.md)

## Expansion

Stability at $x^*$ with $r = 1$ persists, by the implicit function theorem, to a curve of stable positive equilibria for nearby $r$, in particular for $r$ slightly below $1$, where extinction is also stable. The a priori bound turns unboundedness of the continuum into unboundedness of its $r$-spectrum; since the branch starts to the left of $1$ and the spectrum is connected, it covers $r = 1$, giving a positive equilibrium there. Condition A3(b) can fail: in a juvenile–adult example satisfying A1, A2 and A4, the positive state at $r = 1$ can be unstable while a stable positive 2-cycle provides the survival attractor, so a strong Allee effect arises with a cycle instead of an equilibrium. For $r > 1$ extinction is unstable and no strong Allee effect is possible.

## Sources

- J. M. Cushing, "Backward bifurcations and strong Allee effects in matrix models for the dynamics of structured populations", Journal of Biological Dynamics 8(1) (2014) 57–73, Section 3, assumptions A2–A4, Theorem 3, Corollaries 1–2 and the juvenile–adult example of Section 4, <https://doi.org/10.1080/17513758.2014.899638>, PMCID PMC4241602.
