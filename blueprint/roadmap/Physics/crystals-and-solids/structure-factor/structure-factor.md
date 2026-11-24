# Finite structure factor with the negative-exponent kernel

Let `ι` be a finite set of sites, `N ≥ 1` an integer, `f : ι → ℂ` amplitudes and `r : ι → ℤ/Nℤ`
positions on the cyclic group of order `N`. The structure factor at the wavevector index
`k ∈ ℤ/Nℤ` is

`S(k) = ∑_{j ∈ ι} f_j exp(-2π i k r_j / N)`,

where `i` is the imaginary unit, the product `k r_j` is taken in `ℤ/Nℤ`, and any integer
representative of it may be used in the exponential. The kernel has the negative exponent, as in the
discrete Fourier transform on `ℤ/Nℤ` and in Kittel's structure factor `∑_j f_j exp(-i G · r_j)`;
some texts use the opposite sign.
