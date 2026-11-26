# Unclonable encryption

An *unclonable encryption* scheme encrypts a classical message $m$ under a classical key $k$ into a quantum ciphertext $\rho_{k,m}$. *Unclonable security* requires that for any splitting channel applied to $\rho_{k,m}$ producing a bipartite state for two non-communicating parties, who then both receive $k$, the probability that both output $m$ is at most $2^{-|m|}+\mathrm{negl}$ for uniformly random messages (search version), or that both guess a challenge bit with probability at most $1/2+\mathrm{negl}$ (indistinguishability version).

## Depends on

- [Indistinguishability of encryptions with error $\varepsilon$](../security-games/semantic-security-and-indistinguishability/ind-secure.md)
- [No-cloning theorem (linear form)](../../../QuantumInformation/quantum-operations/no-cloning-linear.md)

## Sources

- Anne Broadbent, Sébastien Lord, "Uncloneable Quantum Encryption via Oracles", TQC (2020).
