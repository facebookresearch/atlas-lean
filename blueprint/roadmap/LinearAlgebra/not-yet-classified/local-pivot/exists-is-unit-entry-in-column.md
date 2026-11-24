# Exists is Unit entry in column

Every column of `GL n R` over a commutative local ring contains a unit entry.

Uses `(j,j)` entry of `g⁻¹ * g = 1`, `Matrix.mul_apply`, `IsLocalRing.exists_of_isUnit_sum`
and `IsUnit.mul_iff` via `isUnit_of_mul_isUnit_right`.
