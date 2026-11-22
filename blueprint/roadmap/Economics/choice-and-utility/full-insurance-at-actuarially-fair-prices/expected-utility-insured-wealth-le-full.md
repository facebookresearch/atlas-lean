# Fair full insurance is optimal

For a finite set of states with probabilities `p(x)`, initial wealth `w` and losses `ℓ(x)`, let the
Bernoulli utility `u` be concave on a convex set `S` of wealth levels (a risk-averse agent). For
every indemnity schedule `I` bought at the fair premium `E_p[I] = ∑ₓ p(x) I(x)` whose final wealth
`w - ℓ(x) + I(x) - E_p[I]` lies in `S` in every state, the expected utility
`∑ₓ p(x) u(w - ℓ(x) + I(x) - E_p[I])` is at most that of full insurance, `u(w - E_p[ℓ])`.
