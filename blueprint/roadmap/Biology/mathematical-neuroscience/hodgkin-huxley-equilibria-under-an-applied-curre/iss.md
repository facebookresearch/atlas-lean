# Squid steady-state current–voltage relation

For real `V`, `I∞(V)` is the [steady-state current](../hodgkin-huxley-model/steady-current.md) of
the [squid parameters](../hodgkin-huxley-model/squid.md):

`I∞(V) = 120 m∞(V)³ h∞(V) (V - 115) + 36 n∞(V)⁴ (V + 12) + 0.3 (V - E_L)`,

the ionic current with each gating variable at its steady state
[`m∞`](../hodgkin-huxley-model/m-inf.md), [`h∞`](../hodgkin-huxley-model/h-inf.md),
[`n∞`](../hodgkin-huxley-model/n-inf.md), and `E_L` the
[squid leak reversal potential](../hodgkin-huxley-model/squid-el.md). Here `V` is the
depolarization from rest in mV and `I∞(V)` is in µA/cm². The squid system with applied current
`I` has an equilibrium over `V` exactly when `I∞(V) = I`
([equilibria at current I](field-squid-i-eq-zero-iff.md)).
