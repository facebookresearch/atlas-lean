# Bifurcation of Turing pattern branches

Linear theory of Turing patterns on a finite interval and the local bifurcation of pattern branches.
On $[0, L]$ with Neumann boundary conditions only the discrete wavenumbers $k_n = n\pi/L$ count: for
$d_u, d_v > 0$, $\operatorname{tr} J < 0 < \det J$ and Turing's criterion infinitely many real
wavenumbers are unstable, but only finitely many Neumann modes, none on short intervals, and the
unstable band can fall between two consecutive $k_n^2$. For $\operatorname{tr} J < 0$ and
$d_u, d \ge 0$, as the inhibitor diffusion $d$ increases, an admissible mode
($f_u k^2 - d_u k^4 > 0$) becomes unstable at its neutral diffusion $d_n(k^2)$, where its critical
eigenvalue crosses zero with positive speed (when the trace there is negative). For such a mode, if
a reduced bifurcation map $G$ is strictly differentiable at $(0, d_n(k^2))$ and equals the critical
eigenvalue on the trivial branch $a = 0$ for $d$ near $d_n(k^2)$, the reduced equation
$a\, G(a, d) = 0$ has a local pattern branch $d = \varphi(a)$. If moreover
$G(a, d) = G(0, d) + a^2 H(a, d)$ near $(0, d_n(k^2))$, with $H$ continuous there,
$c = H(0, d_n(k^2)) \neq 0$, and $\partial_a H$ defined near $(0, d_n(k^2))$ and continuous there,
the direction of the branch and its stability in the reduced equation are fixed by the sign of $c$.
Only the selected mode is controlled.

## Eigenvalues of real 2 × 2 matrices

- [A singular real 2 × 2 matrix has exactly the eigenvalues 0 and tr M](exists-eigenvector-iff-of-det-eq-zero.md)

## Finite-domain spectrum versus the continuum of wavenumbers

- [Neumann eigenvalue of the linearized system on an interval](is-neumann-eigenvalue.md)
- [Linear instability on an interval with Neumann boundary conditions](is-neumann-unstable.md)
- [Instability on an interval is instability of some Neumann mode](is-neumann-unstable-iff.md)
- [A Neumann eigenvalue gives a zero-flux solution e^(μt) cos(k_n x) v](exists-solution.md)
- [Instability on an interval implies instability of some real wavenumber](exists-is-unstable-mode.md)
- [For d_u, d_v > 0 and positive discriminant, h < 0 exactly on (q₋, q₊)](set-of-dispersion-det-neg-eq-ioo.md)
- [Under the band condition, infinitely many wavenumbers are unstable](set-of-is-unstable-mode-infinite.md)
- [For stable kinetics, d_u, d_v > 0: no unstable mode on short intervals](exists-forall-not-is-neumann-unstable.md)
- [For tr J < 0, a band between consecutive k_n² leaves no unstable mode](not-is-neumann-unstable-of-gap.md)
- [Turing's criterion: infinitely many unstable k, finitely many k_n](continuum-vs-neumann.md)

## Onset of a Neumann mode as the inhibitor diffusion increases

- [Neutral diffusion d_n(q) of a squared wavenumber](neutral-diffusion.md)
- [For f_u q − d_u q² ≠ 0, h(q) = (f_u q − d_u q²)(d_n(q) − d)](dispersion-det-eq-mul-neutral-diffusion.md)
- [For tr J < 0, an admissible mode is unstable iff d_n(k²) < d](is-unstable-mode-iff-neutral-diffusion-l.md)
- [For tr J < 0 < det J, g_v ≤ 0, inadmissible modes are never unstable](not-is-unstable-mode-of-inadmissible.md)
- [For tr J < 0 < det J, g_v ≤ 0: instability iff an admissible d_n < d](is-neumann-unstable-iff-exists-neutral-d.md)
- [At d_n(k²), with f_u k² ≠ d_u k⁴, the eigenvalues are 0 and the trace](exists-eigenvector-mode-matrix-iff-of-ne.md)
- [Zero is an eigenvalue of the mode matrix iff the mode is neutral](exists-eigenvector-zero-iff.md)
- [Without resonance, only the neutral Neumann mode has eigenvalue 0](set-of-neumann-zero-eigen-eq-singleton.md)

## The critical eigenvalue and its crossing

- [Leading real eigenvalue (tr M + √(tr² M − 4 det M))/2](leading-eigenvalue.md)
- [With a nonnegative discriminant, the leading real eigenvalue is one](exists-eigenvector-leading-eigenvalue.md)
- [A singular matrix with negative trace has leading real eigenvalue 0](leading-eigenvalue-eq-zero.md)
- [At a neutral mode with negative trace, λ₊ has an explicit d-derivative](has-deriv-at-leading-eigenvalue-mode-mat.md)
- [With negative trace, an admissible mode's eigenvalue crosses 0 at d_n](leading-eigenvalue-crossing.md)

## Local pattern branch of the reduced bifurcation equation

- [Transversal zero (0, d₀) of G: near it, a G = 0 iff a = 0 or d = φ(a)](exists-pattern-branch.md)
- [Reduced pattern branch and sign change of the critical eigenvalue](turing-pattern-branch.md)
- [Direction and reduced stability of the pattern branch](pattern-branch-direction-stability.md)
- [Supercritical Turing branches are stable in the reduced equation](turing-pattern-branch-stability.md)

## The reduced equation from the Lyapunov–Schmidt reduction

- [A factor G of the reduced map has G(0, d₀) = 0, ∂_d G(0, d₀) = ψ(L₁φ)](ls-scalar-factor-normalization.md)
- [The Turing linearization is affine in the inhibitor diffusion](mode-operator-eq-add-smul.md)
- [Critical functional normalized by its value on the critical mode](normalized-critical-functional.md)
- [The critical functional on the critical mode is f_v tr(J − κ²D)](critical-functional-critical-mode.md)
- [The critical functional on L₁φ is f_v (d_u κ⁴ − f_u κ²)](critical-functional-mode-operator-critic.md)
- [Turing pattern branch from the Lyapunov–Schmidt reduction](turing-pattern-branch-of-reduction.md)
