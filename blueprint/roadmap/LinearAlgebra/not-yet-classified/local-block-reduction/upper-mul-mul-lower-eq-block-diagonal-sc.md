# Upper mul mul lower eq block Diagonal schur

For an invertible finite block matrix over a commutative ring with
invertible lower-right block `D`, multiply on the left by the upper block
factor with entry `-B * D⁻¹` and on the right by the lower block factor
with entry `-D⁻¹ * C`. The result is `diag(A - B * D⁻¹ * C, D)`.
