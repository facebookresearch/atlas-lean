# Largest finite number

For a binary format with precision $p$ and greatest last-place
exponent $q_{\max}$, this is the real number $M = (2^p - 1) \cdot 2^{q_{\max}}$. It is the largest
finite number of the format: $M$ is a number of the format (`isFloatIn_maxFinite`) and bounds the
absolute value of every number of the format (`abs_le_maxFinite`).
