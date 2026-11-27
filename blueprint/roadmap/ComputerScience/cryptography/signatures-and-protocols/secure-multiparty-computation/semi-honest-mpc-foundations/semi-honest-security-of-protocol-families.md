# Computational semi-honest security of protocol families

A *protocol family* assigns to every security parameter $n$ and public parameters $d$ a protocol $\pi_{n,d}$ and a functionality $f_{n,d}$, with inputs, views and outputs encoded as words. It is *semi-honest secure* for a coalition $I$ if there is a probabilistic polynomial-time simulator family $\mathcal{S}$ such that for every probabilistic polynomial-time environment that chooses $d$ and the inputs and then sees the coalition's views together with all outputs, the advantage between the real and the ideal joint distributions is negligible in $n$. Perfect privacy with polynomial-time simulators implies security, replacing simulators by statistically close ones changes the advantage by at most the distance, and for the empty coalition statistical closeness of outputs suffices.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)
- [Probabilistic polynomial-time Turing machines](../../../security-games/asymptotic-security/probabilistic-polynomial-time-turing-machines.md)
- [Negligible advantage](../../../security-games/asymptotic-security/negligible-adv.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
