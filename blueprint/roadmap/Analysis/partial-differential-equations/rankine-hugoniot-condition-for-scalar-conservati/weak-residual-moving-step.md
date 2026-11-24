# Weak Residual moving Step

Weak residual of a straight moving step. For constant states `uL`, `uR`,
interface `x = c * t`, any flux `f`, and a smooth test `φ` vanishing outside a
bounded rectangle, with partial derivatives `φt`, `φx`:
`∫∫ (u * φ_t + f u * φ_x) = -((f uR - f uL) - c * (uR - uL)) * ∫ φ (t, c * t) dt`.
The time-derivative terms use the moving-interval transport theorem
`ControlVolumes.movingJumpTransport`.
