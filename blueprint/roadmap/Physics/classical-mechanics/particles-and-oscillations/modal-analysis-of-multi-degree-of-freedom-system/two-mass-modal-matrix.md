# Mass-orthonormal modal matrix of two masses and one spring

For real numbers `m₁` and `m₂`, the modal matrix of two masses joined by a spring is

`C = [[1 / √(m₁ + m₂), m₂ / √(m₁ m₂ (m₁ + m₂))], [1 / √(m₁ + m₂), -m₁ / √(m₁ m₂ (m₁ + m₂))]]`:

its columns are the rigid translation `(1, 1)` and the mode `(m₂, -m₁)`, each divided by the square
root of its modal mass, `m₁ + m₂` and `m₁ m₂ (m₁ + m₂)`. For `m₁, m₂ > 0` it is mass-orthonormal
([modal basis](two-mass-modal-basis.md)); with the conventions `√u = 0` for `u < 0` and `u / 0 = 0`
the formula is defined for all real masses.
