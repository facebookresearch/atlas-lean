# Measurement results in the BB84 intercept-resend attack

In an intercept-resend attack on BB84, measuring a bit sent in one basis in
a second basis returns the bit when the two bases agree and the measurer's
fair coin otherwise. Eve measures Alice's bit `a`, sent in the basis `ba`,
in the basis `be` with her coin `ce`: she gets `a` when `be = ba` and `ce`
otherwise. Bob measures Eve's resent bit `e`, encoded in the basis `be`, in
the basis `bb` with his coin `cb`: he gets `e` when `bb = be` and `cb`
otherwise.
