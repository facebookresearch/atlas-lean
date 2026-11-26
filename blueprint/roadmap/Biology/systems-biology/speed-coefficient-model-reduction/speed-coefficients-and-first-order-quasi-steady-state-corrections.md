# Speed coefficients and first-order quasi-steady-state corrections

**Setting.** A biochemical model is a system of ODEs $\dfrac{dx_i}{dt} = f_i(x_1, \dots, x_N)$,
$i = 1, \dots, N$.

**Speed coefficients.** The speed coefficient of $x_i$ is the magnitude of the corresponding diagonal
Jacobian entry,

$$\lambda_i(x_1, \dots, x_N) = \left|\frac{\partial f_i}{\partial x_i}\right|,$$

evaluated along a representative solution, so that $\lambda_i$ becomes a function of time. Variables
are ranked by how quickly they approach their momentary steady state, and the candidate for
elimination is the variable that is "fastest at its slowest": the one maximizing
$\min_t \lambda_i(t)$ over the simulated interval. The heuristic uses only diagonal Jacobian entries,
so each elimination must be confirmed by comparing the reduced and full solutions (for example the
skew subsystem $\dot x = A y$, $\dot y = -A x$ has zero diagonal entries yet oscillates fast for large
$A$).

**QSSA with correction for a linear fast variable.** If the selected variable obeys (after inserting
an artificial small parameter $\varepsilon$)

$$\varepsilon \frac{dx_j}{dt} = \alpha_j(t) - \beta_j(t)\, x_j,$$

with $\alpha_j, \beta_j$ depending on time through the other variables, then expanding
$x_j = x_j^{0} + \varepsilon x_j^{1} + O(\varepsilon^2)$ gives the zeroth-order quasi-steady state
$x_j^{0} = \alpha_j/\beta_j$ and the first-order correction
$x_j^{1} = -\dot x_j^{0}/\beta_j = (\alpha_j \dot\beta_j - \beta_j \dot\alpha_j)/\beta_j^{3}$.
Setting $\varepsilon = 1$, the first-order QSSA is

$$\bar x_j^{1} = \frac{\alpha_j(t)}{\beta_j(t)} + \frac{\alpha_j(t)\dot\beta_j(t) - \beta_j(t)\dot\alpha_j(t)}{\beta_j(t)^3},$$

and the size of the correction term serves as an estimate of the error of the leading-order
approximation. Iterating selection, elimination and validation gives a reduction algorithm.

## Depends on

- [Tikhonov and Anosov theorems for quasi-steady-state reduction](tikhonov-and-anosov-theorems-for-quasi-steady-state-reduction.md)

## Expansion

Substituting the series into the fast equation and matching powers of $\varepsilon$ gives
$0 = \alpha_j - \beta_j x_j^{0}$ at order $\varepsilon^0$ and $\dot x_j^{0} = -\beta_j x_j^{1}$ at order
$\varepsilon^1$. For a genuine Tikhonov system the fast block of the Jacobian is $\varepsilon^{-1}
\partial g/\partial z$ with eigenvalues of order $\varepsilon^{-1}$ and negative real part, so large
diagonal entries are the expected signature of fast variables, which is why the diagonal ranking is
a sensible first filter. Applied to the 14-variable two-feedback NF-κB model (first simplified to 10 equations
by conservation laws and a decoupled variable), repeated elimination reduced it to four ODEs that
kept the limit cycle under continuous TNFα input; zeroth-order QSSAs alone reached five ODEs, and
the last step needed a first-order correction, which also limited the drift of the Hopf point and
the loss of cycle amplitude; a different
representative solution (pulsed input) selected different variables, showing that the reduction
depends on the class of solutions of interest.

## Sources

- S. West, L. J. Bridge, M. R. H. White, P. Paszek, V. N. Biktashev, "A method of 'speed coefficients' for biochemical model reduction applied to the NF-κB system", Journal of Mathematical Biology (2015), <https://doi.org/10.1007/s00285-014-0775-x> (PMC4311267). Section 2.3 (Eq. 5, speed coefficients, selection rule), Section 2.4 (Eqs. 6–12, model reduction algorithm), Sections 3–4.
