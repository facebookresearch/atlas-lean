# Duhamel Deriv

The derivative of `prodIntegral` at `x`, in **Duhamel (Volterra) form**:
`duhamelDeriv x h j = ∑_{i ≤ j} (∏_{l < i} (1 + x l)) · h i · ∏_{i < l ≤ j} (1 + x l)`,
the grid analogue of `h ↦ ∫_{(0, t]} ∏_{(0, s)} (1 + dA) dh(s) ∏_{(s, t]} (1 + dA)`
(Gill–Johansen 1990).
