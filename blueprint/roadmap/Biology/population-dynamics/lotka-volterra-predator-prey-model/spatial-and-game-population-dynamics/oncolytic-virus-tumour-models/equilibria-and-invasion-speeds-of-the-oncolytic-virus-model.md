# Equilibria and invasion speeds of the oncolytic virus infection model

Let $p, q, \beta, K > 0$. The spatially homogeneous version of the [continuum oncolytic virus models](continuum-limits-of-the-oncolytic-virus-agent-based-model.md) is

$$\frac{du}{dt} = p u \Big(1 - \frac{u + i}{K}\Big) - \frac{\beta}{K} u i, \qquad \frac{di}{dt} = \frac{\beta}{K} u i - q i.$$

**Equilibria.** The system has the equilibria $(0, 0)$, $(K, 0)$ and

$$(u^*, i^*) = \Big( \frac{qK}{\beta},\ \frac{pK(\beta - q)}{\beta(\beta + p)} \Big).$$

- $(0, 0)$ has eigenvalues $p$ and $-q$, hence is unstable.
- $(K, 0)$ has eigenvalues $-p$ and $\beta - q$: stable if $\beta < q$ (then $i^* < 0$ and infection dies out from positive data, i.e. treatment fails), unstable if $\beta > q$.
- At $(u^*, i^*)$ the Jacobian has trace $-pq/\beta$ and determinant $pq(\beta - q)/\beta$, so for $\beta > q$ both eigenvalues have negative real part and the coexistence equilibrium is stable.

**Linear spreading speeds (undirected movement).** For $\partial_t u = D_u \partial_{xx} u + f(u) u$ with $f(0) = p$, linearization at $u = 0$ gives the invasion speed $2\sqrt{D_u p}$, the Fisher-KPP minimal speed for $\partial_t u = D \partial_{xx} u + p u (1 - u/K)$. Infected cells invading uninfected tissue at constant density $\hat u$ satisfy $\partial_t i = D_i \partial_{xx} i + (\beta \hat u / K - q) i$, giving speed $2\sqrt{D_i(\beta \hat u / K - q)}$, which is $2\sqrt{D_i(\beta - q)}$ when $\hat u = K$. For the degenerate equation $\partial_t u = (D/K) \partial_x(u \partial_x u) + p u(1 - u/K)$ the minimal speed is $\sqrt{Dp/2}$, and compactly supported data evolve into sharp fronts of compact support.

## Depends on

- [Every Fisher–KPP front speed is at least the minimal speed](../../../../pattern-formation/fisher-kpp-travelling-waves/two-mul-sqrt-le-of-is-front.md)

## Expansion

At the interior equilibrium $\beta u^*/K = q$, so the Jacobian is $\begin{pmatrix} -p u^*/K & -(p + \beta) u^*/K \\ \beta i^*/K & 0 \end{pmatrix}$; its trace is $-pq/\beta$ and its determinant $(p + \beta)\beta u^* i^*/K^2 = pq(\beta - q)/\beta$. Negative trace and positive determinant give stability, with either two negative real eigenvalues or a stable focus. The speeds come from the dispersion relation of the linearized equation $\partial_t w = D w_{xx} + r w$, whose minimal wave speed is $2\sqrt{Dr}$. For the pressure-driven system no rigorous travelling-wave results are known; the paper's numerics show waves from $(0,0)$ to $(u^*, i^*)$ and note that infection cannot invade tissue at carrying capacity because movement stops where the pressure gradient vanishes.

## Sources

- D. Morselli, M. E. Delitala and F. Frascoli, Agent-based and continuum models for spatial dynamics of infection by oncolytic viruses, *Bull. Math. Biol.* 85 (2023), article 92, <https://doi.org/10.1007/s11538-023-01192-x>, PMCID PMC10471645. Section 3, equations (8)-(11).
- R. A. Fisher, The wave of advance of advantageous genes, *Ann. Eugenics* 7 (1937), 355-369, <https://doi.org/10.1111/j.1469-1809.1937.tb02153.x>.
