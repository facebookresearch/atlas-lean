# GMW: oblivious transfer is complete for semi-honest multiparty computation

For every $m$-party deterministic functionality given by a Boolean circuit $C$, the GMW circuit-evaluation protocol in the $\mathrm{OT}^4_1$-hybrid model computes $C$ with perfect semi-honest privacy against every static coalition: each party additively shares each of its input bits among all parties using its private coins; XOR and NOT gates are evaluated locally on shares; each AND gate is evaluated by one invocation of the $m$-party shared multiplication; finally the output shares are sent to their owners. The simulators run in polynomial time, so for circuit families of polynomial size the protocol family is semi-honest secure; composing with any semi-honest secure protocol for $\mathrm{OT}^4_1$ (for example from DDH) gives a semi-honest secure protocol in the plain model for every polynomial-time functionality.

## Proof sketch

Each wire is shared so that every proper coalition's shares are uniform and independent of the honest parties' inputs; shared multiplication is perfectly private, and the composition theorem yields privacy of the whole circuit evaluation, with the coalition's view simulated from its inputs, outputs and uniform shares.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)
- [Computational semi-honest security of protocol families](semi-honest-security-of-protocol-families.md)
- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](../oblivious-transfer-protocols/oblivious-transfer-functionalities.md)

## Proof depends on

- [Shared multiplication from 1-out-of-4 oblivious transfer](ot14-shared-multiplication.md)
- [Composition theorem for semi-honest multiparty protocols](semi-honest-composition-theorem.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
