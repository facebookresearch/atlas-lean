# Fejér polynomial as convolution with the Fejér kernel

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). The normalized Fejér kernel is K_N(x)=circleFejerKernel N x=(N+1)⁻¹|∑_{j=0}^N
e_j(x)|², viewed in ℂ. For x∈𝕋, circleFejerPolynomial f N x=∫ t, f(t)K_N(x-t) ∂μ.
