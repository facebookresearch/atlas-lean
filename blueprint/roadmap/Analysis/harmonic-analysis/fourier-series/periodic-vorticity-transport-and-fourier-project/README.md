# Periodic vorticity transport and Fourier projection cancellation

Work with finite complex Fourier coefficients on the period-$2\pi$ torus.
The physical derivative has multiplier $ik_j$, and $q(k)=|k|^2=k_0^2+k_1^2$.
Set $\psi_k=-p_k/q(k)$, with the reciprocal at zero equal to zero, and
$u=(-D_1\psi,D_0\psi)$. Then $\operatorname{div}u=0$; when $p_0=0$, its curl
$D_0u_1-D_1u_0$ is $p$. Positive transport is $C(p)=u\cdot\nabla p$;
the convective evolution term is $-C(p)$.

The zero coefficient of a product is its normalized mean. Integration by parts
and the Jacobian product rule give cancellation against vorticity and against
streamfunction. Exact projection onto a finite symmetric frequency set preserves
these pairings against supported input. Hermitian coefficients convert them to
complex coefficient sums, including the inverse-frequency weight for kinetic
energy. No closure of the retained set under addition is assumed.

Sources for the classical periodic Fourier model:
[Agrachev–Sarychev, section 2.2](https://control.botik.ru/wp-content/files_mf/1434657132navier.pdf)
and [Bedrossian–Punshon-Smith (2024), section 1.1](https://link.springer.com/article/10.1007/s00220-024-04949-0).
The orientation and signs here are fixed by the displayed definitions.

- [Jacobian bracket of finite Fourier polynomials](bracket.md)
- [The Jacobian bracket has zero mean](bracket-coeff-zero.md)
- [Jacobian product rule in the second argument](bracket-mul-right.md)
- [Jacobian product rule in the first argument](bracket-mul-left.md)
- [Cancellation against the second bracket argument](bracket-pair-self-right.md)
- [Cancellation against the first bracket argument](bracket-pair-self-left.md)
- [Exact projection onto a finite frequency set](project.md)
- [Coefficients of exact Fourier projection](project-coeff.md)
- [Projection fixes supported polynomials](project-eq-self.md)
- [Projection preserves pairing against supported input](project-pair.md)
- [Symmetric projection preserves Hermitian reality](project-2.md)
- [Inverse-Laplacian streamfunction](stream-function.md)
- [Finite vorticity transport](transport.md)
- [Bilinear vorticity transport cancellation](transport-enstrophy-cancel.md)
- [Bilinear streamfunction transport cancellation](transport-energy-cancel.md)
- [Streamfunction support does not grow](stream-function-support.md)
- [Projected bilinear vorticity cancellation](project-transport-enstrophy-cancel.md)
- [Projected bilinear streamfunction cancellation](project-transport-energy-cancel.md)
- [Physical Laplacian on finite Fourier polynomials](laplacian.md)
- [Fourier coefficients of the Laplacian](laplacian-coeff.md)
- [Only the zero frequency has zero weight](weight-eq-zero-iff.md)
- [Frequency weight is even](weight-neg.md)
- [Inverse Laplacian recovers zero-mean vorticity](laplacian-stream-function.md)
- [Velocity reconstructed from finite vorticity](velocity.md)
- [Reconstructed velocity is divergence-free](velocity-divergence.md)
- [Curl recovers zero-mean vorticity](velocity-curl.md)
- [Streamfunction reconstruction preserves reality](stream-function-2.md)
- [Nonzero square Fourier cutoffs](square-modes.md)
- [Membership in a square cutoff](mem-square-modes.md)
- [Square cutoffs are symmetric](square-modes-symmetric.md)
- [Transport equals reconstructed velocity advection](transport-eq-velocity.md)
- [Negation preserves Hermitian reality](neg.md)
- [Subtraction preserves Hermitian reality](sub.md)
- [Jacobian brackets preserve Hermitian reality](bracket-2.md)
- [Vorticity transport preserves Hermitian reality](transport-2.md)
- [Oriented determinant of two frequencies](determinant.md)
- [Jacobian interaction of two Fourier modes](bracket-single.md)
- [Exact vorticity convection coefficient formula](transport-coeff.md)
- [Transport as an actual physical Jacobian](physical-lift-transport.md)
- [Projected support lies in the retained modes](project-support.md)
- [Hermitian coefficient pairing as a zero mode](pairing-eq-coeff-zero.md)
- [Complex enstrophy cancellation after projection](sum-project-transport-enstrophy-cancel.md)
- [Complex kinetic-energy cancellation after projection](sum-project-transport-energy-cancel.md)
