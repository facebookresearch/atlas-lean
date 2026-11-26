# Fourier coefficient of a Fejér polynomial

Let 𝕋=UnitAddCircle=ℝ/ℤ, with normalized Haar probability measure μ=AddCircle.haarAddCircle.
Write e_k(x)=fourier k x and f̂(k)=∫ x:𝕋, f(x)e_(-k)(x) ∂μ for k∈ℤ. For f∈L∞(𝕋,μ) and N∈ℕ, let
F_N(f)=circleFejerPolynomial f N be the continuous Fejér polynomial (N+1)⁻¹∑_{0≤i,j≤N}
f̂(i-j)e_(i-j). Put w_N(k)=circleFejerWeight N k=(N+1-|k|)_+/(N+1), viewed as a complex
scalar, where (·)_+ is truncation at zero. For every k∈ℤ, fourierCoeff(F_N(f))
k=w_N(k)*fourierCoeff f k. Thus the coefficient is zero for |k|>N, and the zero-frequency
coefficient equals f̂(0), including N=0.
