# Finite Fourier polynomials on the two-dimensional torus

Write $p_k$ for a finitely supported complex coefficient family on $\mathbb Z^2$.
Its unit-torus realization is $R(p)(y)=\sum_k p_k e^{2\pi i k\cdot y}$; its
physical lift on $\mathbb R^2$ is $L_p(x)=\sum_k p_k e^{i k\cdot x}$, periodic
with period $2\pi$ in each coordinate. Multiplication is exact convolution.
The physical derivative is $D_jp$ with coefficients $i k_jp_k$, and conjugation
is $p^\#_k=\overline{p_{-k}}$. All integrals on the unit torus use normalized
Haar probability measure.

These conventions are those of the classical periodic Fourier model in
Agrachev–Sarychev, *Navier-Stokes Equations: Controllability by Means of Low Modes
Forcing*, section 2.2, and Bedrossian–Punshon-Smith, *Chaos in Stochastic 2d
Galerkin-Navier-Stokes* (2024), section 1.1. The physical derivative convention
and the conversion $a_k=2\pi p_k$ to TorusSobolev coefficients are explicit below.

- [Finite Fourier coefficient algebra](polynomial.md)
- [Realization by torus characters](realize.md)
- [Realization of a single Fourier mode](realize-single.md)
- [Recovery of finite Fourier coefficients](coefficient-realize.md)
- [Frequency multipliers on finite polynomials](multiplier.md)
- [Coefficients of a frequency multiplier](multiplier-coeff.md)
- [A multiplier acting on one mode](multiplier-single.md)
- [Physical Fourier derivative multiplier](derivative.md)
- [Coefficients of the physical derivative](derivative-coeff.md)
- [Product rule for finite Fourier convolution](derivative-mul.md)
- [Commutation of Fourier coordinate derivatives](derivative-commute.md)
- [Normalized Parseval for finite Fourier polynomials](parseval.md)
- [Realization on the period-2pi torus](physical.md)
- [Periodic lift of a Fourier polynomial](physical-lift.md)
- [Physical lift of one Fourier mode](physical-lift-single.md)
- [Conjugation of finite Fourier polynomials](conjugate.md)
- [Coefficients after polynomial conjugation](conjugate-coeff.md)
- [Addition of physical polynomial lifts](physical-lift-add.md)
- [Scalar multiplication of physical lifts](physical-lift-smul.md)
- [Actual coordinate derivatives of Fourier polynomials](has-deriv-at-physical-lift.md)
- [Conjugation of one Fourier mode](conjugate-single.md)
- [Conjugate linearity of polynomial conjugation](conjugate-smul.md)
- [Pointwise realization of polynomial conjugation](realize-conjugate.md)
- [Hermitian symmetry of Fourier coefficients](is-real.md)
- [Hermitian polynomials are fixed by conjugation](conjugate-eq.md)
- [Hermitian coefficients give real functions](realize-im.md)
- [Products preserve Hermitian symmetry](mul.md)
- [Physical derivatives preserve Hermitian symmetry](derivative-2.md)
- [Real part of the physical realization](real-physical.md)
- [Rescaling a Hermitian physical realization](unit-representative.md)
- [Conversion to TorusSobolev coefficient normalization](fourier-coefficient.md)
- [Mean of a finite Fourier polynomial](integral-realize.md)
- [Physical derivatives have zero mean coefficient](derivative-coeff-zero.md)
- [Integration by parts for finite Fourier polynomials](integration-by-parts.md)
- [Involution of polynomial conjugation](conjugate-conjugate.md)
- [Hermitian symmetry as a fixed-point condition](is-real-iff-conjugate-eq.md)
- [Sums preserve Hermitian symmetry](add.md)
- [Multipliers preserving Hermitian symmetry](multiplier-2.md)
