# Aimd Step

One synchronous AIMD step: if the total exceeds `goal`, every load is
multiplied by `b`; otherwise every load increases by `a`. This is the
linear control of Chiu--Jain Section 1.3 with `a_I = a`, `b_I = 1`,
`a_D = 0`, `b_D = b` (paper example (3)).
