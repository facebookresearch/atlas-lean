# Weak Residual moving Step eq zero iff of trace ne zero

A test with nonzero interface integral detects the jump: for a smooth test `φ` vanishing
outside a bounded rectangle, with time and space partials `φt`, `φx`, and
`∫ φ (t, c * t) dt ≠ 0` (a positive one such as `interfaceTest`), the weak residual of the
moving step vanishes exactly when `c * (uR - uL) = f uR - f uL`.
