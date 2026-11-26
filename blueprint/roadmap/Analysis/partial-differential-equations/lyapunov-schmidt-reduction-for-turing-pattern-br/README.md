# Lyapunov–Schmidt reduction for Turing pattern branches

The steady states of the two-species Turing system on $[0, \ell]$ with Neumann boundary conditions
near a homogeneous state are the zeros of a map $F(w, d)$ (perturbation $w$, inhibitor diffusion
$d$) with the trivial branch $F(0, d) = 0$. For a map $F$ between Banach spaces that vanishes at
$(0, p_0)$, is strictly differentiable there and whose state derivative $L$ has a Fredholm package,
the Lyapunov–Schmidt reduction solves the range part of $F = 0$ by the implicit function theorem and
leaves a finite-dimensional bifurcation equation. When $\ker L$ is spanned by one vector and
$\operatorname{range} L$ is the kernel of a functional (codimension at most one), this is a scalar
equation; along a trivial branch $F(0, d) = 0$, a factorization $\tilde G(a, d) = a\, G(a, d)$ near
$(0, d_0)$ with $G$ strictly differentiable at $(0, d_0)$, $G(0, d_0) = 0$ and
$\partial_d G(0, d_0) \neq 0$, and the reduced branch theorem for $G$, give the pattern branch of
$F$. For the Turing linearization on finitely many cosine modes, a critical mode with $f_v \neq 0$
and no resonant mode gives a one-dimensional kernel and a range of codimension one. The reduction
applies to any Banach-space formulation of the steady-state problem once a Fredholm package of its
linearization is given.

## Fredholm packages and projections

- [Projection onto the kernel part of a Fredholm package](ker-proj.md)
- [Projection onto the cokernel part of a Fredholm package](coker-proj.md)
- [Every x splits as π₀x + π₁x along a Fredholm package](ker-proj-add-proj.md)
- [Every y splits as Qy + (1 − Q)y along a Fredholm package](proj-add-coker-proj.md)
- [L vanishes on the kernel part of its Fredholm package](apply-coe-x.md)
- [On the essential part, Q ∘ L is the package isomorphism](proj-apply-coe-x.md)

## The Lyapunov–Schmidt reduction

- [Lyapunov–Schmidt ansatz (z, p, w) ↦ (z + w, p)](ls-embed.md)
- [Lyapunov–Schmidt splitting (x, p) ↦ ((π₀x, p), π₁x)](ls-split.md)
- [Range equation of the Lyapunov–Schmidt reduction](ls-range-map.md)
- [The range map's derivative in the essential component is A](ls-range-map-deriv-inr.md)
- [Lyapunov–Schmidt solution operator W](ls-solution.md)
- [Reduced bifurcation map g(z, p) = (1 − Q) F(z + W(z, p), p)](ls-reduced.md)
- [If F(0, p₀) = 0, the range equation near it holds exactly on graph W](eventually-ls-range-map-eq-zero-iff.md)
- [If F(0, p₀) = 0, the solution operator vanishes at (0, p₀)](ls-solution-zero.md)
- [Lyapunov–Schmidt reduction near a zero of F](lyapunov-schmidt.md)
- [The solution operator is strictly differentiable at (0, p₀), ∂_z W = 0](exists-has-strict-fderiv-at-ls-solution.md)
- [On a trivial branch, W(0, p) = 0 and g(0, p) = 0](eventually-ls-solution-zero.md)

## Reduction to a scalar equation

- [Scalar bifurcation function ψ(F(aφ + W(aφ, p), p))](ls-scalar.md)
- [If ψ cuts out range L, the scalar function has exactly the zeros of g](ls-scalar-eq-zero-iff.md)
- [Coordinate of the kernel component along φ](ker-coord.md)
- [Lyapunov–Schmidt reduction to a scalar equation near a zero of F](lyapunov-schmidt-scalar.md)
- [On a trivial branch, the scalar bifurcation function vanishes at a = 0](eventually-ls-scalar-zero.md)
- [For φ ≠ 0, the kernel coordinate tends to 0 at x = 0](tendsto-ker-coord.md)

## Pattern branches of the full problem

- [Pattern branch of F(x, d) = 0 from the reduced branch theorem](lyapunov-schmidt-pattern-branch.md)

## Kernel and range of singular 2 × 2 matrices

- [Kernel vector (m₀₁, −m₀₀) of a singular 2 × 2 matrix](ker-vec.md)
- [For det M = 0 and m₀₁ ≠ 0, the kernel of M is ℝ(m₀₁, −m₀₀)](mul-vec-eq-zero-iff-of-det-eq-zero.md)
- [For det M = 0 and m₀₁ ≠ 0, the range of M is m₁₁y₀ − m₀₁y₁ = 0](exists-mul-vec-eq-iff-of-det-eq-zero.md)

## The Turing linearization on Neumann modes

- [Linearized Turing operator on coefficients of finitely many modes](mode-operator.md)
- [The off-diagonal entry m₀₁ of every mode matrix is f_v](mode-matrix-zero-one.md)
- [Critical functional from the row (m₁₁, −f_v) of mode i₀](critical-functional.md)
- [Field of finitely many cosine modes ∑ cos(κᵢ x) wᵢ](mode-field.md)
- [On mode fields, D u″ + J u is the mode operator on the coefficients](diffusion-mul-vec-deriv-deriv-add.md)
- [Every mode field has zero derivative at x = 0](deriv-mode-field-zero.md)
- [A field of Neumann modes has zero derivative at x = ℓ](deriv-mode-field-neumann.md)

## Kernel and range at a critical mode

- [Critical mode: the kernel vector of the mode matrix in mode i₀](critical-mode.md)
- [For f_v ≠ 0, the critical mode is nonzero](critical-mode-ne-zero.md)
- [For f_v ≠ 0 and a simple critical mode i₀, the kernel is ℝφ](mode-operator-eq-zero-iff.md)
- [For f_v ≠ 0 and a simple critical mode i₀, the range is ker ψ](exists-mode-operator-eq-iff.md)
- [The mode operator on finitely many modes is Fredholm](is-fredholm-mode-operator.md)
- [For f_v ≠ 0 and a simple critical mode, every package has kernel ℝφ](mode-operator-simple-kernel.md)
