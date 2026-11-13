# Conditional estimate as a fit to the first-block residual

Unconditionally, the conditional formula equals the nonsingular-inverse formula applied to
the algebraic residual `y - X₁ ((X₁ᵀX₁)⁻¹ X₁ᵀ y)`. If both Gram determinants are units, these
are the successive least-squares fits on blocks 1 and 2. With a singular Gram matrix they need
not minimize residual error. This is in general not the block-2 part of the joint formula on
both blocks (the formulas agree when `X₂ᵀX₁ = 0`).
