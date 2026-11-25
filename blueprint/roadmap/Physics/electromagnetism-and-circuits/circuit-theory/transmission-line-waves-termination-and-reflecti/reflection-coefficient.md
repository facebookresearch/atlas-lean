# Reflection coefficient of a load on a line

For a complex load impedance `Z_L` and a real characteristic impedance `Z₀`, the reflection
coefficient is

`Γ = (Z_L − Z₀) / (Z_L + Z₀)`.

The intended domain is `Z_L + Z₀ ≠ 0`; with the convention `x / 0 = 0`, `Γ = 0` at `Z_L = −Z₀`,
where, for `Z₀ > 0`, the [passivity criterion](passive-load-reflection.md)
[fails](reflection-criterion-fails-at-excluded-l.md).
