# Public-key quantum money and quantum lightning

A *public-key quantum money* scheme consists of quantum polynomial-time algorithms $\mathsf{Gen}(1^\lambda)\to(\mathsf{sk},\mathsf{pk})$, $\mathsf{Mint}(\mathsf{sk})\to(s,|\$_s\rangle)$ producing a classical serial number and a banknote, and $\mathsf{Ver}(\mathsf{pk},s,\rho)\in\{0,1\}$, such that honest banknotes verify (and remain verifiable after verification) and no efficient adversary given $\mathsf{pk}$ and one banknote with serial $s$ outputs two states that both verify for $s$, except with negligible probability. *Quantum lightning* strengthens this: anyone (without $\mathsf{sk}$) can mint banknotes, yet no efficient adversary, even one generating its own states, can produce two states that verify for the same serial number.

## Depends on

- [Wiesner's private-key quantum money](wiesner-quantum-money.md)

## Sources

- Scott Aaronson, "Quantum Copy-Protection and Quantum Money", CCC (2009), arXiv:1110.5353.
- Scott Aaronson, Paul Christiano, "Quantum Money from Hidden Subspaces", STOC (2012), arXiv:1203.4740.
- Mark Zhandry, "Quantum Lightning Never Strikes the Same State Twice", EUROCRYPT (2019).
