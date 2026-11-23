# Mohr–Coulomb resisting shear stress on the slip plane

For an effective cohesion `c`, a friction angle `φ`, a unit weight `γ`, a vertical depth `z`, a
slope angle `β` and a slip-plane pore pressure `u` (real numbers), the Mohr–Coulomb resisting
shear stress, a model input, is `τR = c + (σn - u) * tan φ`, where `σn = γ * z * cos β ^ 2` is the
normal stress and `σn - u` the compression-positive effective normal stress (Biot coefficient
one). It is defined for all real inputs, with `tan φ = sin φ / cos φ` and the convention
`x / 0 = 0`: where `cos φ = 0`, for instance at `φ = π / 2`, the friction term is `0` and
`τR = c`. The intended domain is `c ≥ 0` and `0 ≤ φ < π / 2`.
