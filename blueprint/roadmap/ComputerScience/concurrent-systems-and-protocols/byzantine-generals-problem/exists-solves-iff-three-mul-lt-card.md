# The Byzantine generals problem with oral messages is solvable exactly when there are more than `3 m` generals

**The Byzantine generals problem with oral messages is solvable exactly when there are more
than `3 m` generals** (Lamport, Shostak and Pease). Let the generals form a finite type with at
least three elements, and let there be at least two orders. Some `OralProtocol` whose state and
message types lie in `Type (max u v)` solves the problem with commander `c` and at most `m`
traitors, in some number of rounds, if and only if `3 m` is less than the number of generals. In
that case `OM(m)` solves it in `m + 1` rounds (`OralMessages.solves_toProtocol`); otherwise no
protocol, in any universe, solves it
(`Impossibility.OralProtocol.not_solves_of_card_le_three_mul`).
