# Payoff to debtholders at maturity

For real terminal firm value `V` and face value `F`, the risky-debt payoff is `min(V, F)`: debt
holders are paid in full when the firm can pay, and take the whole firm otherwise. This reading
needs `0 ≤ V` and `0 ≤ F`; for other real arguments `min(V, F)` is the total algebraic extension,
and the payoff identity `min(V, F) + max(V - F, 0) = V` holds for all real `V` and `F`.
