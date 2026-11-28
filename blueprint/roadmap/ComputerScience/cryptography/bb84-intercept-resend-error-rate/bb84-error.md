# Error event of the BB84 intercept-resend attack

For Alice's bit `a`, Bob's fair coin `cb`, and the bases `ba`, `be`, `bb` of
Alice, Eve and Bob (booleans, with `false` for the Z basis and `true` for
the X basis), `bb84Error a cb ba be bb` is the boolean that is true exactly
when the round is sifted (`bb = ba`), Eve measured in the other basis (`be ≠
ba`), and Bob's coin differs from Alice's bit (`cb ≠ a`).

This is the closed form of the event that a sifted round of the
intercept-resend attack ends with Bob's result differing from Alice's bit;
it does not depend on Eve's coin.
