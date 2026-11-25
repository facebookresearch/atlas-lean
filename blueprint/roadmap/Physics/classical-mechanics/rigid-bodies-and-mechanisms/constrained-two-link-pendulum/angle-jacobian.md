# Derivative of the angle-to-position map

For real `l₁`, `l₂` and angles `q = (q₁, q₂)`, the angle derivative is the linear map sending
angular velocities `w = (w₁, w₂)` to the pair of plane vectors

`(l₁ w₁ (cos q₁, sin q₁), l₁ w₁ (cos q₁, sin q₁) + l₂ w₂ (cos q₂, sin q₂))`,

the [velocities of the two masses](angle-jacobian-apply.md). It is the
[derivative](has-fderiv-at-pos-map.md) at `q` of the [angle-to-position map](pos-map.md).
