# Bounded classical Burgers initial value uniqueness

For positive viscosity, the initial values determine a jointly continuous,
positive-time jointly $C^2$ classical Burgers solution that is uniformly bounded
on each finite strip. Finite-strip conclusions retain the half-line regularity
and equation hypotheses. No derivative of the initial velocity is required.

For the initial-time inverse profile, define
$M_a(t)=\int_a^{a+1}(a+1-y)u(t,y)\,dy$ and
$R_a(t)=(4\nu)^{-1}\int_a^{a+1}u(t,y)^2\,dy-(u(t,a+1)-u(t,a))/2$.
The normalization is
$N_a(t)=(M_a(t)-M_a(0))/(2\nu)+\int_0^tR_a(s)\,ds$.
Thus its positive inverse profile has exactly the anchored exponential of the
initial velocity at time zero. Heat uniqueness identifies it with the Gaussian
heat evolution, and its logarithmic derivative recovers the Burgers velocity.

- [Initial-time inverse normalization gives the heat evolution](initial-inverse-profile-eq-heat-solution.md)
- [Identification of bounded classical Burgers solutions on a strip](eq-burgers-solution-on-strip.md)
- [Uniqueness of bounded classical Burgers solutions on a strip](burgers-eq-on-strip.md)
- [Identification of stripwise bounded Burgers solutions](eq-burgers-solution.md)
- [Uniqueness for stripwise bounded classical Burgers solutions](burgers-eq.md)
