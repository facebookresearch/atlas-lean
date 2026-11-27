# The SIDH key exchange and its torsion point information

Let $p=2^{a}3^{b}f-1$ be prime, $E_0/\mathbb{F}_{p^{2}}$ supersingular with known $\mathrm{End}(E_0)$, and $(P_A,Q_A)$, $(P_B,Q_B)$ bases of $E_0[2^{a}]$ and $E_0[3^{b}]$. Alice samples $s_A$, computes $\varphi_A:E_0\to E_A$ with kernel $\langle P_A+[s_A]Q_A\rangle$ and publishes $(E_A,\varphi_A(P_B),\varphi_A(Q_B))$; Bob does the symmetric operation. Both derive the shared $j$-invariant of $E_0/\langle P_A+[s_A]Q_A,P_B+[s_B]Q_B\rangle$. The *torsion point information* $(\varphi_A(P_B),\varphi_A(Q_B))$ reveals the action of the secret $2^{a}$-isogeny on $E_0[3^{b}]$.

## Depends on

- [Supersingular elliptic curves and isogenies](../supersingular-isogenies-and-quaternion-orders/supersingular-curves.md)

## Sources

- David Jao, Luca De Feo, "Towards Quantum-Resistant Cryptosystems from Supersingular Elliptic Curve Isogenies", PQCrypto (2011).
