# Fully polymorphic equilibria and the maximum migration rate

Use the model, notation and boundary equilibria of [Boundary equilibria of the two-locus continent–island model](boundary-equilibria-of-the-two-locus-continent-island-model.md), with $0 < \alpha \le \beta$ and $\rho > 0$.

**Explicit internal equilibria.** Let $R = \sqrt{(\alpha+\beta+\rho)^2 - 8m\rho}$. The only possible fully polymorphic equilibria are $E_\pm$ with

$$\hat p_\pm = \frac{1}{8\alpha\rho}\Big[\beta^2 - \alpha^2 + 6\alpha\rho - \rho^2 - 4m\rho \pm (\alpha - \beta + \rho)R\Big],$$

$$\hat q_\pm = \frac{1}{8\beta\rho}\Big[\alpha^2 - \beta^2 + 6\beta\rho - \rho^2 - 4m\rho \pm (\beta - \alpha + \rho)R\Big],$$

and $\hat D_\pm$ determined by $\dot p = 0$. They are real iff

$$m \le m^* = \frac{(\alpha+\beta+\rho)^2}{8\rho},$$

and $E_+ = E_-$ iff $m = m^*$.

**Proposition 1 (admissibility).** With $m_C = \alpha+\beta-\rho$ and $m_B = \alpha(1 + (\beta-\alpha)/\rho)$:

(a) $E_+$ lies in the state space iff exactly one of
- $0 < \rho \le \min(\alpha, \tfrac13(\alpha+\beta))$ and $0 < m < m_C$;
- $\tfrac13(\alpha+\beta) < \rho \le 3\alpha - \beta$ and $0 < m < m^*$;
- $\max(\alpha, 3\alpha-\beta) < \rho$ and $0 < m < m_B$

holds. Thus $E_+$ exists for all positive $m$ below a critical value.

(b) $E_-$ lies in the state space iff $\beta < 2\alpha$ and either $\tfrac13(\alpha+\beta) < \rho \le \alpha$ and $m_C < m < m^*$, or $\alpha < \rho < 3\alpha - \beta$ and $m_B < m < m^*$. In particular $E_-$ never exists when $\beta \ge 2\alpha$.

**Theorems 2–3 (bifurcation structure).** For $\alpha < \beta$ the equilibrium configurations as functions of $m$ fall into seven cases determined by $\rho$ relative to $\alpha$, $\tfrac13(\alpha+\beta)$ and $3\alpha-\beta$ (and, for $\beta < 2\alpha$, one further threshold); for $\alpha = \beta$ there are four cases, separated by $\rho = \tfrac23\alpha$, $\alpha$ and $2\alpha$. Polymorphism is lost at $m_C$ when linkage is tight ($\rho \le \tfrac23\alpha$ suffices) and at $m_B$ when it is loose ($\rho > 2\alpha$ suffices).

## Depends on

- [Boundary equilibria of the two-locus continent–island model](boundary-equilibria-of-the-two-locus-continent-island-model.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Substituting $D$ from $\dot p = 0$ into $\dot D = 0$ leaves an equation linear in $q$; inserting its solution into $\dot q = 0$ gives a quadratic in $p$ with discriminant $R^2$, whence the closed forms and the threshold $m^*$. $E_+$ tends to $E_I$ as $m \to 0$ and to $E_0$ as $\rho \to 0$. In the intermediate-linkage regime ($\beta < 2\alpha$) $E_+$ and $E_-$ coexist and annihilate in a saddle-node bifurcation at $m^*$, so $E_+$ can coexist with a stable boundary equilibrium. For $\alpha = \beta$ the coexistence interval is maximized at $\rho = \alpha$, where $m^* = \tfrac98\alpha$: migration slightly above the single-locus threshold $\alpha$ can still be resisted thanks to linkage.

## Sources

- R. Bürger, A. Akerman, "The effects of linkage and gene flow on local adaptation: a two-locus continent–island model", Theoretical Population Biology 80(4) (2011) 272–288, Eqs. (3.15)–(3.31), Proposition 1, Theorems 2–3, <https://doi.org/10.1016/j.tpb.2011.07.002>, PMCID PMC3257863.
