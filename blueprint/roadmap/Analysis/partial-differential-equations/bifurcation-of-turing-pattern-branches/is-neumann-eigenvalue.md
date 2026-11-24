# Is Neumann Eigenvalue

`μ` is an eigenvalue of the linearization `w ↦ D w_xx + J w` on `[0, L]` with homogeneous
Neumann boundary conditions: it is an eigenvalue of the mode matrix `J - k_n² D` of some
admissible Neumann wavenumber `k_n = n π / L`. Only the discrete wavenumbers `k_n` contribute;
the continuum of wavenumbers `k ∈ ℝ` of the problem on the whole line does not. (That these are
all eigenvalues of the PDE operator, i.e. completeness of the cosine basis, is not proved here;
the definition records the spectrum it induces.)

The definition is total in `L`, but only `0 < L` is a Neumann domain. With Lean's `x / 0 = 0`
every `k_n` vanishes at `L = 0`, so the predicate then reduces to `μ` being an eigenvalue of `J`
itself; for `L < 0` it equals the predicate for `-L`, since only `k_n²` enters.
