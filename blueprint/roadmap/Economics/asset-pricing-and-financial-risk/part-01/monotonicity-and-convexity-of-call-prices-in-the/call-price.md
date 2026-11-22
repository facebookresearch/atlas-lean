# Call Price

Call price at strike `K` under the state prices `ψ` and terminal underlying values `S`:
`C(K) = ∑ ω, ψ ω * europeanCallPayoff (S ω) K` (source clause: "call price =
state-price-weighted call payoff"). `ψ ω` is the state price of state `ω`; `S ω` is the
terminal underlying value in state `ω`. The payoff is the landed
`OptionPayoffs.europeanCallPayoff`, not a re-encoding of `max (S - K) 0`.
