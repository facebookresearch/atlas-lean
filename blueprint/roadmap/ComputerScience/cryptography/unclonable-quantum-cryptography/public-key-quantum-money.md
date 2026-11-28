# Public-key quantum money and quantum lightning

A *public-key quantum money* scheme consists of polynomial-time quantum algorithms $\mathsf{KeyGen}(0^{n})\to(k_{\mathrm{private}},k_{\mathrm{public}})$, $\mathsf{Bank}(k_{\mathrm{private}})$ producing a banknote (usually a pair $(s,\rho_s)$ of a classical serial number and a quantum state), and $\mathsf{Ver}(k_{\mathrm{public}},\cdot)$, which accepts or rejects an alleged banknote. Valid banknotes are accepted with probability at least $2/3$ (completeness error at most $1/3$, which can be amplified), and the scheme is sound if, for every $q=\mathrm{poly}(n)$ and every polynomial-size counterfeiter that receives $k_{\mathrm{public}}$ and $q$ valid banknotes and outputs $\mathrm{poly}(n)$ possibly entangled alleged banknotes, the probability that more than $q$ of the outputs are accepted is negligible, whatever their serial numbers. A *mini-scheme* is the narrower primitive with only $\mathsf{Bank}(0^{n})\to(s,\rho_s)$ and $\mathsf{Ver}$, whose soundness requires that no polynomial-size counterfeiter given one banknote $(s,\rho_s)$ outputs two possibly entangled states that are both accepted for the same serial $s$, except with negligible probability; a secure public-key money scheme yields a secure mini-scheme. *Quantum lightning* strengthens the mini-scheme game: anyone (without a secret key) can mint banknotes, yet no efficient adversary, even one generating its own states, can produce two states that verify for the same serial number.

## Depends on

- [Wiesner's private-key quantum money](wiesner-quantum-money.md)

## Sources

- Scott Aaronson, "Quantum Copy-Protection and Quantum Money", CCC (2009), arXiv:1110.5353.
- Scott Aaronson, Paul Christiano, "Quantum Money from Hidden Subspaces", STOC (2012), arXiv:1203.4740.
- Mark Zhandry, "Quantum Lightning Never Strikes the Same State Twice", EUROCRYPT (2019).
