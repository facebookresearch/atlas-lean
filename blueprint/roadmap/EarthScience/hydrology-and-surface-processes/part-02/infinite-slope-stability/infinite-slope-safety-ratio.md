# Safety ratio of resisting to driving shear stress

For a resisting shear stress `τR`, a unit weight `γ`, a vertical depth `z` and a slope angle `β`
(real numbers), the safety ratio is `τR / τd`, with the driving stress
`τd = γ * z * sin β * cos β`. It is defined for all real inputs, with the convention `x / 0 = 0`:
it is `0` when `τd = 0`, for instance on a horizontal slope `β = 0`. The intended domain is a
genuine slope, `γ > 0`, `z > 0` and `0 < β < π / 2`, where `τd > 0`.
