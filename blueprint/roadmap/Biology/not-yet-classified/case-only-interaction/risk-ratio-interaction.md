# Risk Ratio Interaction

The risk-ratio interaction `SRR = RR_ge / (RR_g RR_e)` for cell masses `a, …, h` (cases and
non-cases at `(G, E) = (0, 0), (1, 0), (0, 1), (1, 1)`), where each relative risk compares the risk
in a cell with the risk `a / (a + b)` in the doubly unexposed cell. It is meaningful for positive
cell masses; if any denominator is `0`, Lean's convention `x / 0 = 0` applies.
