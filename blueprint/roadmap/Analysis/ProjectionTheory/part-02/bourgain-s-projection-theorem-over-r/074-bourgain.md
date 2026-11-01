---
article_id: af_0992aeaef123a682e8648f12
declaration: theorem
origin: cited
statement: formalized
lean: BourgainProjection.bourgain_projection
---

# Theorem (Bourgain)

Let $0 < t < 2$, $0 < s \leq 1$. Then there exist $\varepsilon, \eta > 0$, both functions of $s, t$, such that for all $X$ with $|X| = R^t$, $D$ with $|D| = R^s$, if for all $x \in B_R$, $r \leq R$, $\theta \in [0,1]$, $\rho \in [0,1]$ we have $$|X \cap B(x, r)| \leq R^\eta \left(\frac{r}{R}\right)^t |X|, \quad |D \cap B(\theta, \rho)| \leq R^\eta \rho^s |D|,$$ then there exists some $\theta \in D$ such that $$\inf_{Y \subset X,\, |Y| \geq R^{-\eta} |X|} |\pi_\theta Y| \geq R^{t/2 + \varepsilon}.$$

## Depends on

This node has no prerequisites.

## Sources

- [MIT 18.156 Projection Theory (Spring 2025), Section: Bourgain's projection theorem over R, part 1, Subsection: Real case](../../../../../sources/v1/ProjectionTheory.md)
