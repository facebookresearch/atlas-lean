# Soundness error for false statements

Under special soundness, a cheating prover for a
statement `x` with **no witness at all** (`hx`) answers at most one challenge per commitment, so it
convinces the honest verifier with probability at most `1 / |Ch|`.

This is soundness for the language of true statements, not knowledge soundness. The hypothesis
`hx` says that `x` is false, which is much stronger than saying that the prover does not know an
existing witness. In the Schnorr setting with a generator `g` of the order-`q` subgroup every
statement has a witness, so `hx` never holds there, and this theorem does not model the
impersonator of Katz and Lindell, Theorem 12.11. A knowledge-soundness statement needs a rewinding
(knowledge-extraction) experiment, which is not defined here.
