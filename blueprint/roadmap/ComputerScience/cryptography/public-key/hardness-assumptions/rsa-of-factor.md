# Rsa Of Factor

The RSA inverter built from a factoring algorithm `F` (Katz and Lindell, Section 8.2.4: "if
factoring is easy, RSA is easy"): factor `n` as `(a, b)`, invert `e` modulo `(a - 1)(b - 1)`,
and output `y ^ (e⁻¹ mod (a - 1)(b - 1))`.
