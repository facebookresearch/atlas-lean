# Composition theorem for semi-honest multiparty protocols

Let $\pi$ be a protocol in the $\mathcal{F}$-hybrid model for a functionality $g$ (the oracle world $W_1$ answers each oracle call $op$ by the functionality $\mathcal{F}_{op}$), and for every $op$ let $\rho_{op}$ be a protocol in a world $W_2$ computing $\mathcal{F}_{op}$. Let $\pi^\rho$ replace every oracle call by an execution of the corresponding subprotocol. For a coalition $I$, simulators $\mathcal{S}_1$ for $\pi$ and $\mathcal{S}_{2, op}$ for $\rho_{op}$, and the composed simulator that runs $\mathcal{S}_1$ and expands the simulated oracle answers by $\mathcal{S}_{2,op}$: for every distinguisher $D$,

$$
\mathrm{Adv}_{\pi^\rho}(D) \le \mathrm{Adv}_{\pi}(D') + \sum_{\text{oracle rounds } j} \mathbb{E}\bigl[\mathrm{Adv}_{\rho_{op_j}}(D_j)\bigr]
$$

for explicit distinguishers $D'$ and round distinguishers $D_j$, the expectation taken over the outer execution up to round $j$. In particular, if $\pi$ is perfectly private in the $\mathcal{F}$-hybrid model and every $\rho_{op}$ perfectly privately computes $\mathcal{F}_{op}$, then $\pi^\rho$ perfectly privately computes $g$. Any randomized functionality reduces to a deterministic one by sharing the coins additively among the parties, so the theorem also covers randomized functionalities.

## Proof sketch

Both the composed real execution and the ideal execution with the composed simulator are a common kernel program applied to, respectively, the real joints and the ideal joints of the subprotocols; a hybrid over the oracle rounds replaces them one at a time.

## Depends on

- [Synchronous oracle-aided multiparty protocols and perfect semi-honest privacy](oracle-aided-protocols-and-perfect-privacy.md)
- [Sequential composition for semi-honest security](../sequential-composition-for-semi-honest-security.md)

## Proof depends on

- [Hybrid argument](../../../security-games/games-and-advantages/advantage-le-sum.md)

## Sources

- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
