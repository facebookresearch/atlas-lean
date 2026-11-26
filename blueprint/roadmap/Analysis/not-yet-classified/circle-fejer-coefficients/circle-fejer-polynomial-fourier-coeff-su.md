# Fourier coefficient from the finite Fejér difference sum

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). For k∈ℤ, F_N(f)̂(k)=(N+1)⁻¹ circleDifferenceSum N k (f̂(k)), where
circleDifferenceSum counts the pairs 0≤i,j≤N with i-j=k.
