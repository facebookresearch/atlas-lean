# $\mathsf{PubK}^{\mathrm{eav}}$ with fixed messages is the indistinguishability experiment

For an eavesdropper whose two challenge messages $(m_0, m_1)$ do not depend on the public key or on
its coins, the left-or-right eavesdropping experiment $\mathsf{PubK}^{\mathrm{eav}}$ with
challenge bit $b$ is the [indistinguishability experiment](ind-exp.md) on $m_b$, with the
eavesdropper's guess as distinguisher.

## Sources

- J. Katz and Y. Lindell, *Introduction to Modern Cryptography*, 2nd ed., CRC Press, 2014,
  Definition 11.2 (the experiment $\mathsf{PubK}^{\mathrm{eav}}$).
