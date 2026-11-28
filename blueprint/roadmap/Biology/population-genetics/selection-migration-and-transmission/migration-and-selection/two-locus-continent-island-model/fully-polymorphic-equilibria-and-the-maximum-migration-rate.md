# Fully polymorphic equilibria and the maximum migration rate

Use the model, notation and boundary equilibria of [Boundary equilibria of the two-locus continent–island model](boundary-equilibria-of-the-two-locus-continent-island-model.md), with $0 < \alpha \le \beta$ and $\rho > 0$.

**Explicit internal equilibria.** Let $R = \sqrt{(\alpha+\beta+\rho)^2 - 8m\rho}$. The only possible fully polymorphic equilibria are $E_\pm$ with

$$\hat p_\pm = \frac{1}{8\alpha\rho}\Big[\beta^2 - \alpha^2 + 6\alpha\rho - \rho^2 - 4m\rho \pm (\alpha - \beta + \rho)R\Big],$$

$$\hat q_\pm = \frac{1}{8\beta\rho}\Big[\alpha^2 - \beta^2 + 6\beta\rho - \rho^2 - 4m\rho \pm (\beta - \alpha + \rho)R\Big],$$

and $\hat D_\pm$ determined by $\dot p = 0$. They are real iff

$$m \le m^* = \frac{(\alpha+\beta+\rho)^2}{8\rho},$$

and $E_+ = E_-$ iff $m = m^*$.

**Proposition 1 (admissibility).** With $m_C = \alpha+\beta-\rho$ and $m_B = \alpha(1 + (\beta-\alpha)/\rho)$, call an equilibrium *internal* if all four gamete frequencies are positive, i.e. it lies in the interior of the state space $S_4$:

(a) $E_+$ is an internal equilibrium iff exactly one of
- $0 < \rho \le \min(\alpha, \tfrac13(\alpha+\beta))$ and $0 < m < m_C$;
- $\tfrac13(\alpha+\beta) < \rho < 3\alpha - \beta$ and $0 < m \le m^*$, or $\rho = 3\alpha - \beta > \tfrac13(\alpha+\beta)$ and $0 < m < m^*$;
- $\max(\alpha, 3\alpha-\beta) < \rho$ and $0 < m < m_B$

holds. Thus $E_+$ is internal for all positive $m$ below a critical value.

(b) $E_-$ is an internal equilibrium iff $\beta < 2\alpha$ and either $\tfrac13(\alpha+\beta) < \rho \le \alpha$ and $m_C < m \le m^*$, or $\alpha < \rho < 3\alpha - \beta$ and $m_B < m \le m^*$. In particular $E_-$ is never internal when $\beta \ge 2\alpha$.

Internal is stronger than lying in $S_4$. At $m = 0$ the point $E_+$ is the vertex $E_I$, in $S_4$ but not internal, and $E_-$ can also lie on the boundary: for $\alpha = 1$, $\beta = 3$, $\rho = 4$, $m = 0$ it is the vertex $E_C$. At $m = m^*$ the merged point $E_+ = E_-$ is internal in the ranges above: since $m^* - m_C = (\alpha+\beta-3\rho)^2/(8\rho)$ and $m^* - m_B = (\rho - 3\alpha + \beta)^2/(8\rho)$, $m^*$ lies strictly above the exit values $m_C$ and $m_B$ for $\tfrac13(\alpha+\beta) < \rho < 3\alpha - \beta$, and the merged point is internal there, whereas at $\rho = 3\alpha - \beta$ one has $m^* = m_B$ and the merged point is the boundary equilibrium $E_B$. For example $\alpha = \beta = \rho = 1$, $m = m^* = \tfrac98$ gives $E_+ = E_-$ with $(\hat p, \hat q, \hat D) = (\tfrac1{16}, \tfrac1{16}, \tfrac3{256})$ and gamete frequencies $(\tfrac1{64}, \tfrac3{64}, \tfrac3{64}, \tfrac{57}{64})$.

*Correction to the source.* The source's Proposition 1 writes the upper bounds in (3.17b) and (3.18) as the strict $m < m^*$, which excludes the internal merged equilibrium at $m = m^*$; its own bifurcation description has $E_+$ and $E_-$ merging at $m = m^*$ inside the state space. The statement above closes those bounds except at $\rho = 3\alpha - \beta$, where the merged point is $E_B$.

**Theorems 2–3 (bifurcation structure).** For $\alpha < \beta$ the equilibrium configurations as functions of $m$ fall into seven cases determined by $\rho$ relative to $\alpha$, $\tfrac13(\alpha+\beta)$ and $3\alpha-\beta$ (and, for $\beta < 2\alpha$, one further threshold); for $\alpha = \beta$ there are four cases, separated by $\rho = \tfrac23\alpha$, $\alpha$ and $2\alpha$. Polymorphism is lost at $m_C$ when linkage is tight ($\rho \le \tfrac23\alpha$ suffices) and at $m_B$ when it is loose ($\rho > 2\alpha$ suffices).

## Depends on

- [Boundary equilibria of the two-locus continent–island model](boundary-equilibria-of-the-two-locus-continent-island-model.md)

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Substituting $D$ from $\dot p = 0$ into $\dot D = 0$ leaves an equation linear in $q$; inserting its solution into $\dot q = 0$ gives a quadratic in $p$ with discriminant $R^2$, whence the closed forms and the threshold $m^*$. $E_+$ tends to $E_I$ as $m \to 0$ and to $E_0$ as $\rho \to 0$. In the intermediate-linkage regime ($\beta < 2\alpha$) $E_+$ and $E_-$ coexist and annihilate in a saddle-node bifurcation at $m^*$, so $E_+$ can coexist with a stable boundary equilibrium. For $\alpha = \beta$ the coexistence interval is maximized at $\rho = \alpha$, where $m^* = \tfrac98\alpha$: migration slightly above the single-locus threshold $\alpha$ can still be resisted thanks to linkage.

## Sources

- R. Bürger, A. Akerman, "The effects of linkage and gene flow on local adaptation: a two-locus continent–island model", Theoretical Population Biology 80(4) (2011) 272–288, Eqs. (3.15)–(3.31), Proposition 1 (its "admissible internal equilibrium" is the internal equilibrium here; the strict bounds $m < m^*$ in (3.17b) and (3.18) are corrected as explained above), Theorems 2–3, <https://doi.org/10.1016/j.tpb.2011.07.002>, PMCID PMC3257863.
