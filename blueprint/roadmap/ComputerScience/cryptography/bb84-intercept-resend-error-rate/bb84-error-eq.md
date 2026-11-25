# Closed form of the BB84 sifted error event

For all booleans `a`, `cb`, `ba`, `be`, `bb` and Eve's coin `ce`, `bb84Error
a cb ba be bb` equals the boolean `(bb = ba) ∧ (bb84BobResult (bb84EveResult
a ba be ce) be bb cb ≠ a)`.

Thus the closed-form error event is exactly the event that the round is
sifted and Bob's result, obtained by measuring Eve's resent result, differs
from Alice's bit, whatever the value of Eve's coin.
