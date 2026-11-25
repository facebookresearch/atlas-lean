# Net power of a black surface is emission minus absorption

Let `ι` be a finite set of surfaces with areas `A` and view factors `F` forming a
[black enclosure](is-black-enclosure.md), let `σ > 0` and let the temperatures `T_i ≥ 0` be
absolute. Then for every surface `i`,

`P_i = A_i E(T_i) - ∑_j A_j F_{ji} E(T_j)`, where `E(T) = ∫₀^{π/2} (σ T⁴ / π) cos θ · 2π sin θ dθ`

is the hemispheric integral of the Lambertian intensity `σ T⁴ / π`, the blackbody emissive power
(equal to `σ T⁴`). So the [net power](net-power.md) is the power emitted by `i` minus the power
arriving from every surface and absorbed.
