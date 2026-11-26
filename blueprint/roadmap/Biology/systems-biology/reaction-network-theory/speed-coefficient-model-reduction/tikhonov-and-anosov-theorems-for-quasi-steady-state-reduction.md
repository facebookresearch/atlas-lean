# Tikhonov and Anosov theorems for quasi-steady-state reduction

**Setting.** A **Tikhonov system** with small parameter $\varepsilon > 0$ has slow variables $x$ and fast
variables $z$:

$$\frac{dx}{dt} = f(x, z, t), \qquad \varepsilon \frac{dz}{dt} = g(x, z, t).$$

Its formal limit $\varepsilon \to 0$ is the **reduced (slow) system**
$\dfrac{dx}{dt} = f(x, z, t)$, $z = \phi(x, t)$, where $\phi(x,t)$ solves $g(x, z, t) = 0$, and the
**attached (fast) system** is $\dfrac{dz}{ds} = g(x, z, t)$ with $x, t$ frozen as parameters.

**Theorem (Tikhonov, finite time).** Assume the right-hand sides are smooth enough for existence and
uniqueness. Let $(X(t;\varepsilon), Z(t;\varepsilon))$, $t \in [0, T]$, solve the full system from
$(x_0, z_0)$, and let $\bar X(t)$ solve the reduced system from $x_0$. Suppose that along
$\{(\bar X(t), t) : t \in [0,T]\}$ the root $z = \phi(\bar X(t), t)$ is an isolated, Lyapunov stable and
asymptotically stable equilibrium of the attached system, and that $z_0$ lies in the basin of
attraction of $\phi(x_0, 0)$. Then for every $t \in (0, T]$,

$$\lim_{\varepsilon \to 0} X(t;\varepsilon) = \bar X(t), \qquad \lim_{\varepsilon \to 0} Z(t;\varepsilon) = \phi(\bar X(t), t).$$

**Theorem (Anosov, periodic orbits).** If in addition the reduced system has a periodic solution of
period $P_0$ that is stable in the linear approximation, then for small $\varepsilon$ the full system
has a family of periodic solutions with periods $P(\varepsilon) \to P_0$, whose orbits lie in a small
neighbourhood of the reduced orbit lifted to $z = \phi(x)$; the orbits and periods depend smoothly on
$\varepsilon$.

A **1-parametric embedding** of $\dot u = f(u)$ is a family $\dot u = F(u; \varepsilon)$ with
$F(u; 1) \equiv f(u)$; it is a **Tikhonov embedding** when it has the slow–fast form above. Applying the
theorems to a biochemical model requires choosing such an embedding (which is never unique) and
validating it by checking that solutions converge as $\varepsilon$ decreases toward $0$.

## Expansion

The full trajectory consists of an initial layer of duration $O(\varepsilon)$, during which $x \approx
x_0$ and $z$ relaxes along the attached system in the fast time $s = t/\varepsilon$, followed by slow
motion on the surface $z = \phi(x,t)$. For fixed $t > 0$ the layer has expired once $\varepsilon$ is
small, which gives the pointwise limit; uniformity as $t \to 0$ fails because of the layer. Anosov's
result upgrades closeness on finite intervals to persistence of hyperbolic limit cycles, which is what
justifies reducing oscillatory signalling models such as NF-κB while keeping the oscillation period.

## Sources

- S. West, L. J. Bridge, M. R. H. White, P. Paszek, V. N. Biktashev, "A method of 'speed coefficients' for biochemical model reduction applied to the NF-κB system", Journal of Mathematical Biology (2015), <https://doi.org/10.1007/s00285-014-0775-x> (PMC4311267). Section 2.1, Theorems 1 and 2 (special cases of Tikhonov 1952, Theorem 1, and Anosov 1960, Theorem 5), Section 2.2, Definition 1.
