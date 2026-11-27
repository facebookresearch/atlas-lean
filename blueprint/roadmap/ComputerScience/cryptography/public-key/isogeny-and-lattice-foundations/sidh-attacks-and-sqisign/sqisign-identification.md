# The SQIsign identification protocol

Let $E_0$ have a known special endomorphism ring $\mathcal{O}_0$. The prover's secret is an isogeny $\tau:E_0\to E_A$ (equivalently a left $\mathcal{O}_0$-ideal $I_\tau$, which reveals $\mathrm{End}(E_A)$); the public key is $E_A$. In one round: the prover sends a commitment curve $E_1$ obtained by a secret random isogeny $\psi:E_0\to E_1$ of large smooth degree; the verifier sends a challenge isogeny $\varphi:E_1\to E_2$ of degree $2^{e}$ (encoded by a kernel generator); the prover, knowing $\mathrm{End}(E_A)$ and $\mathrm{End}(E_2)$ through ideals, computes a response isogeny $\sigma:E_A\to E_2$ of degree $2^{e'}$ such that $\hat{\varphi}\circ\sigma$ is cyclic (non-backtracking), by converting the connecting ideal $\overline{I_\tau}I_\psi I_\varphi$ into an equivalent ideal of $2$-power norm (via a KLPT-type algorithm). The verifier checks that $\sigma$ is a valid isogeny from $E_A$ to $E_2$ of the right degree and the non-backtracking condition.

## Depends on

- [The Deuring correspondence between supersingular curves and maximal orders](../supersingular-isogenies-and-quaternion-orders/deuring-correspondence.md)
- [KLPT: ideals of powersmooth or prime-power norm in a special maximal order](../supersingular-isogenies-and-quaternion-orders/klpt-algorithm.md)

## Sources

- Luca De Feo, David Kohel, Antonin Leroux, Christophe Petit, Benjamin Wesolowski, "SQISign: Compact Post-Quantum Signatures from Quaternions and Isogenies", ASIACRYPT (2020), IACR ePrint 2020/1240.
