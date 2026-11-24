# Fick's laws and the diffusion equation

## Fick's first law and the diffusion equation

- [Fick's first law: the flux is −D times the concentration gradient](fick-flux.md)
- [Fick's law with the continuity equation gives the diffusion equation](fick-continuity-imply-diffusion.md)

## The Gaussian on the line

- [Gaussian concentration with total mass M on the line](gauss.md)
- [Spatial derivative of the Gaussian for D > 0 and t > 0](gauss-xderiv-value.md)
- [Second spatial derivative of the Gaussian for D > 0 and t > 0](gauss-xxderiv-value.md)
- [Time derivative of the Gaussian for D > 0 and t > 0](gauss-tderiv-value.md)
- [For D > 0 and t > 0 the Gaussian solves the diffusion equation](gauss-pde.md)

## Mass and the initial limit of the Gaussian

- [For M, D and t positive the Gaussian is nonnegative](gauss-nonneg.md)
- [For D > 0 and t > 0 the Gaussian has total mass M](gauss-mass.md)
- [For M > 0 the Gaussian tends to the point mass M δ₀ as t → 0⁺](gauss-weak-limit.md)

## The complementary error function

- [Complementary error function](erfc.md)
- [Derivative function of the complementary error function](erfc-deriv.md)
- [Second-derivative function of the complementary error function](erfc-deriv2.md)
- [The complementary error function equals 1 at 0](erfc-zero.md)
- [The complementary error function has derivative −2e^−x²/√π](has-deriv-at-erfc.md)
- [The derivative −2e^−x²/√π has derivative 4x e^−x²/√π](has-deriv-at-erfc-deriv.md)
- [The complementary error function solves y″ + 2x y′ = 0](erfc-ode.md)
- [The complementary error function is strictly decreasing](erfc-strict-anti.md)
- [The complementary error function tends to 0 at +∞](erfc-tendsto-at-top.md)
- [For u ≥ 0 the complementary error function is a Gaussian tail integral](erfc-tail.md)
- [The complementary error function is nonnegative for u ≥ 0](erfc-nonneg.md)
- [For u ≥ 0 the complementary error function is at most 2√2 e^−u²/2](erfc-le-gauss.md)

## The error-function profile

- [Error-function profile with surface concentration cs](erfc-profile.md)
- [Spatial derivative of the error-function profile for D, t > 0](erfc-profile-xderiv-value.md)
- [Second spatial derivative of the error-function profile for D, t > 0](erfc-profile-xxderiv-value.md)
- [Time derivative of the error-function profile for D, t > 0](erfc-profile-tderiv-value.md)
- [For D, t > 0 the error-function profile solves the diffusion equation](erfc-profile-pde.md)

## Surface, far-field and initial values

- [For D, t > 0 the error-function profile equals cs at the surface](erfc-profile-surface.md)
- [For D, t > 0 the error-function profile tends to 0 as x → ∞](erfc-profile-farfield.md)
- [For x > 0 and D > 0 the profile tends to 0 as t → 0⁺](erfc-profile-initial.md)

## Mass uptake through the surface

- [For cs, D and t positive the profile is integrable on the half-line](erfc-profile-integrable-on.md)
- [For x, cs and D positive the concentration at depth x increases in t](profile-pointwise-lt.md)
- [For cs, D > 0 the amount on the half-line increases strictly in time](erfc-profile-mass-strict-mono.md)

## Uniqueness for the Dirichlet problem

- [For a ≤ b and continuous w the energy is continuous on 0 ≤ t ≤ T](continuous-on-energy.md)
- [With zero boundary values the energy has derivative −2D ∫ wx²](energy-identity-deriv.md)
- [For D > 0 the Dirichlet problem has at most one solution](diffusion-unique-dirichlet.md)

## Parabolic scaling

- [Parabolic rescaling of a concentration field](scaled-sol.md)
- [Parabolic rescaling of a solution at one point](similarity-pde-at.md)
- [For λ > 0 parabolic rescaling maps solutions on the plane to solutions](similarity-pde.md)
- [Similarity variable of the diffusion equation](sim-var.md)
- [For D, t and λ positive the similarity variable is scaling invariant](sim-var-invariant.md)

## The steady membrane profile

- [Linear steady profile between two boundary concentrations](steady-profile.md)
- [The steady profile equals c₁ at x = 0](steady-boundary-zero.md)
- [For L > 0 the steady profile equals c₂ at x = L](steady-boundary-l.md)
- [The steady profile has the constant slope c₂ − c₁ over L](steady-xderiv-value.md)
- [For L > 0 the steady profile solves the steady diffusion equation](steady-pde.md)
- [For L > 0 the steady membrane flux is D times c₁ − c₂ over L](steady-flux.md)

## The slab sine series

- [Sine coefficients of a uniform initial concentration](fourier-coeff.md)
- [Terms of the slab sine series](fourier-term.md)
- [For L > 0 and n ≥ 1 the sine-coefficient integral gives bₙ](fourier-coeff-formula.md)
- [For t ≥ δ > 0 the series terms are bounded by a geometric sequence](fourier-term-bound.md)
- [For L, D and δ positive the geometric bounds are summable](fourier-dominator-summable.md)
- [For c₀ ≥ 0 and δ > 0 the slab series converges uniformly for t ≥ δ](fourier-uniform-convergent.md)
