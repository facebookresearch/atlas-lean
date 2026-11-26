# Caputo fractional-order compartmental models and Matignon stability

**Caputo derivative.** For $0 < \alpha < 1$ and an absolutely continuous function $f$ on $[0, T]$, the
Caputo fractional derivative is

$$ {}^{C}\!D^{\alpha}_{t} f(t) = \frac{1}{\Gamma(1 - \alpha)} \int_0^t (t - s)^{-\alpha} f'(s)\, ds ,$$

a convolution of $f'$ with a power-law memory kernel; it reduces to $f'$ as $\alpha \to 1$ and
annihilates constants, so equilibria are the same as for the ordinary model.

**Fractional compartmental models.** A fractional epidemic or within-host infection model replaces
each time derivative by ${}^{C}D^{\alpha}_t$. Writing each rate parameter $\kappa$ as $\kappa^{\alpha}$
keeps both sides in units of $(\text{time})^{-\alpha}$. For example, an SEIQR model with transmission
from exposed and infectious classes reads

$$ {}^{C}D^{\alpha}_t S = \Lambda^{\alpha} - \mu^{\alpha} S - \beta^{\alpha} S (E + I), \qquad
 {}^{C}D^{\alpha}_t E = \beta^{\alpha} S (E + I) - (\pi^{\alpha} + \mu^{\alpha} + \gamma^{\alpha}) E,$$

$$ {}^{C}D^{\alpha}_t I = \pi^{\alpha} E - (\sigma^{\alpha} + \mu^{\alpha}) I, \qquad
 {}^{C}D^{\alpha}_t Q = \gamma^{\alpha} E + \sigma^{\alpha} I - (\theta^{\alpha} + \mu^{\alpha}) Q, \qquad
 {}^{C}D^{\alpha}_t R = \theta^{\alpha} Q - \mu^{\alpha} R .$$

**Positivity.** If ${}^{C}D^{\alpha}_t x_i \ge 0$ whenever $x_i = 0$ (with the other coordinates
nonnegative), the nonnegative orthant is positively invariant; this follows from the generalized mean
value theorem $f(t) = f(0) + \frac{1}{\Gamma(\alpha + 1)} {}^{C}D^{\alpha} f(\xi)\, t^{\alpha}$ for some
$\xi \in [0, t]$. Bounds such as $\limsup_t S(t) \le \Lambda^{\alpha}/\mu^{\alpha}$ follow from the
fractional comparison principle applied to ${}^{C}D^{\alpha}_t S \le \Lambda^{\alpha} - \mu^{\alpha} S$.

**Matignon's theorem.** The linear system ${}^{C}D^{\alpha}_t x = A x$ with $0 < \alpha < 1$ is
asymptotically stable if and only if every eigenvalue $\lambda$ of $A$ satisfies

$$|\arg \lambda| > \frac{\alpha \pi}{2},$$

in which case solutions decay like $t^{-\alpha}$ (Mittag-Leffler decay) rather than exponentially.
Hence an equilibrium of a nonlinear Caputo system is locally asymptotically stable if the eigenvalues
of its Jacobian satisfy this sector condition; in particular, $\mathcal{R}_0 < 1$, which places all
eigenvalues at the disease-free equilibrium in the open left half-plane, suffices for every
$\alpha \in (0, 1)$.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/README.md)

## Expansion

Solutions of ${}^{C}D^{\alpha} x = \lambda x$ are $x(t) = E_{\alpha}(\lambda t^{\alpha}) x(0)$, where
$E_{\alpha}(z) = \sum_{k \ge 0} z^k / \Gamma(\alpha k + 1)$ is the Mittag-Leffler function, and
$E_{\alpha}(\lambda t^{\alpha}) \to 0$ exactly when $|\arg \lambda| > \alpha\pi/2$. The stability
region is therefore larger than the left half-plane: eigenvalues with small positive real part but
large imaginary part can still be stable, so fractional order can stabilize an endemic equilibrium
that oscillates or is unstable in the integer-order model. Because the equilibria and the
next-generation threshold do not depend on $\alpha$, the memory parameter changes transient speed
and the shape of epidemic curves rather than the threshold $\mathcal{R}_0 = 1$. Global stability of
the disease-free state is typically proved with Volterra-type Lyapunov functions using the inequality
${}^{C}D^{\alpha}_t\bigl(x - x^* - x^* \ln(x/x^*)\bigr) \le (1 - x^*/x)\, {}^{C}D^{\alpha}_t x$.

## Sources

- Z. Zhang, A. Zeb, O. F. Egbelowo, V. S. Erturk, "Dynamics of a fractional order mathematical model
  for COVID-19 epidemic", Advances in Difference Equations 2020 (2020) 420, model (3), Theorems 1-4,
  <https://doi.org/10.1186/s13662-020-02873-w> (PMC7427275).
- A. N. Chatterjee, B. Ahmad, "A fractional-order differential equation model of COVID-19 infection
  of epithelial cells", Chaos, Solitons and Fractals 147 (2021) 110952, Definition 1, Theorems 1-3
  and the stability condition $|\arg \lambda| > \alpha\pi/2$, <https://doi.org/10.1016/j.chaos.2021.110952>
  (PMC8086832).
