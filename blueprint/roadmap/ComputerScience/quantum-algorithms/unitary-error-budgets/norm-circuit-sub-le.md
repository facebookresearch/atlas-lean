# Error budget for replacing unitary gates

Let `n` be a finite type and let `U V : Fin T → Matrix n n ℂ` be two
sequences of unitary matrices with `‖U i - V i‖ ≤ ε i` in the operator norm
for each `i`. Then the chronological circuit products satisfy `‖circuitProd
U - circuitProd V‖ ≤ ∑ i, ε i`: gate errors add at most linearly.
