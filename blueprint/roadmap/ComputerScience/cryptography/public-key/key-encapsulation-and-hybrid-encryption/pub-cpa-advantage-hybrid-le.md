# Security of hybrid encryption

Suppose the data-encapsulation mechanism generates uniform keys and encrypts $m$ under $k$ as
$E(k, m, s)$ for $s$ drawn from a fixed distribution $\rho$. For every eavesdropping adversary $A$
against the hybrid scheme,

$$\mathrm{Adv}^{\mathrm{eav}}(A) \le \mathrm{Adv}^{\mathrm{kem}}(B_1) + \mathrm{Adv}^{\mathrm{kem}}(B_0) + \mathrm{Adv}^{\mathrm{cpa}}(C),$$

where $B_b$ is the KEM adversary built from $A$ and the bit $b$, and $C$ is the eavesdropper against
the data-encapsulation mechanism built from $A$, which makes no queries (Katz and Lindell,
Theorem 11.12, concrete form). The proof is a three-step hybrid argument.
