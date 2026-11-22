# Cash-and-carry replicates the forward payoff

Cash-and-carry consists of a long position in one unit of the underlying, which pays the
terminal spot price `S(ω)` plus a known terminal income `inc`, financed by borrowing `S0` at
the gross rate `R`. Its terminal payoff `(S(ω) + inc) - S0 R` equals the long-forward payoff
`S(ω) - F` in every state `ω` when `F = S0 R - inc` (all quantities real, with no sign
conditions).
