# Eavesdropping security implies CPA security for public-key encryption

Suppose $\mathrm{Enc}_{pk}(m)$ is the distribution of $E(pk, m, \rho)$ for $\rho$ uniform on a finite
nonempty set. A chosen-plaintext adversary $A$ that makes at most $n$ encryption queries has exactly
the advantage in $\mathrm{PubK}^{\mathrm{cpa}}$ that the simulating eavesdropper built from $A$, $E$
and $n$ has in $\mathrm{PubK}^{\mathrm{eav}}$: Katz and Lindell's Proposition 11.3, as an equality.
