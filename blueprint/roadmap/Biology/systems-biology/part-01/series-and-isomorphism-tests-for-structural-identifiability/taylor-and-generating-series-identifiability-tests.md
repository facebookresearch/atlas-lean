# Taylor-series and generating-series tests for structural identifiability

**Setting.** Consider the model

$$\dot x(t) = f(x(t),\theta) + \sum_{i=1}^{m} g_i(x(t),\theta)\,u_i(t),\qquad y(t) = h(x(t),\theta),\qquad x(0) = x_0(\theta),$$

with state $x \in \mathbb{R}^n$, input $u \in \mathbb{R}^m$, output $y \in \mathbb{R}^p$, and parameter $\theta$ in an open connected set $\Theta \subseteq \mathbb{R}^q$; $f$, $g_i$, $h$ and $x_0$ are analytic. The model is *structurally globally identifiable* at $\theta$ if $y(\cdot\,;\theta') \equiv y(\cdot\,;\theta)$ for all admissible inputs implies $\theta' = \theta$, and *locally identifiable* if this holds for $\theta'$ in some neighbourhood of $\theta$. A vector $\phi(\theta)$ of quantities determined by the output is an *exhaustive summary* if it carries all the information about $\theta$ contained in $y$; then global (local) identifiability is equivalent to global (local) injectivity of $\theta \mapsto \phi(\theta)$.

**Taylor-series test.** Since $y$ is analytic in $t$, it is determined by its derivatives at $t = 0$. Put

$$a_k(\theta) = \left.\frac{d^k y}{dt^k}\right|_{t=0},\qquad k = 0,1,2,\dots$$

If for some finite $k_{\max}$ the algebraic system $a_k(\theta') = a_k(\theta)$, $0 \le k \le k_{\max}$, has the unique solution $\theta' = \theta$ in $\Theta$, the model is structurally globally identifiable at $\theta$; uniqueness only in a neighbourhood gives local identifiability.

**Generating-series test.** Let $L_F \lambda = \sum_j F_j\,\partial \lambda/\partial x_j$ denote the Lie derivative of a function $\lambda$ along a vector field $F$. The coefficients of the Fliess generating series of $y$ with respect to time and inputs are the iterated Lie derivatives

$$h(x_0),\quad L_{f}h(x_0),\quad L_{g_i}h(x_0),\quad L_f L_{g_i} h(x_0),\quad L_{g_j}L_f h(x_0),\ \dots$$

evaluated at $x_0(\theta)$. These coefficients form an exhaustive summary; if a finite subset of them determines $\theta$ uniquely, the model is globally identifiable. A rank test on the Jacobian of a finite set of coefficients with respect to $\theta$ (the *identifiability tableau*) gives local identifiability when the rank equals $q$.

Both tests are sufficient but not necessary: no general a priori bound on the number of coefficients is available for nonlinear models, so failure at a given order does not prove non-identifiability.

## Expansion

Two parameter values producing the same output for every input have the same output derivatives of every order at $t=0$, hence the same Taylor coefficients; for input-affine models the derivatives of $y$ are polynomial in the input and its derivatives with coefficients given by iterated Lie derivatives, which is why the generating-series coefficients are output-determined. Conversely, analyticity means the full coefficient sequence determines $y$, so these sequences are exhaustive summaries. Known order bounds exist only for special classes: for a linear model of state dimension $n$, $2n-1$ derivatives suffice. The generating-series coefficients are usually simpler expressions in $\theta$ than the raw Taylor coefficients, which is the practical reason to prefer them; arranging their nonzero partial derivatives in a tableau exposes columns (parameters) that never appear and suggests an order in which to solve for the parameters one block at a time.

## Sources

- Chis OT, Banga JR, Balsa-Canto E, "Structural identifiability of systems biology models: a critical comparison of methods", PLoS One (2011), Methods: "Structural identifiability definition", "Taylor series approach" (Eqs. (6)–(8)), "Generating series approach" (Eq. (9)) and "Identifiability tableaus", <https://doi.org/10.1371/journal.pone.0027755>, PMCID PMC3222653.
