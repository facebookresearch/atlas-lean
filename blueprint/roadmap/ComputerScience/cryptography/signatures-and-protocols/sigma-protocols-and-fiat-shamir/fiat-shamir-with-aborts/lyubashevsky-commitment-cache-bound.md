# Fresh Lyubashevsky commitments rarely hit a random-oracle cache

Let $q$ be prime, $A \in \mathbb{Z}_q^{n\times m}$ uniform, and let a history depending on $A$ choose a cache $\mathcal{C}$ of at most $Q$ commitment values before a fresh mask $y$ is drawn uniformly from $[-\gamma, \gamma]^m$. Then

$$
\Pr\bigl[A y \in \mathcal{C}\bigr] \le Q\,\bigl(q^{-n} + (2\gamma + 1)^{-m}\bigr),
$$

averaged over $A$, including attempts whose response later aborts. The published commitment of the public simulator, which accepts with the exact acceptance factor, hits the cache with at most that factor times the corresponding bound for the inner box. Hence replacing every hash read of the all-attempt signer by fresh programming changes the joint law of signatures and cache by at most $K q_S$ times this bound.

## Proof sketch

For $y \ne 0$ and prime $q$, $Ay$ is uniform over a uniform $A$; the event $y = 0$ has probability $(2\gamma+1)^{-m}$. Apply a union bound over the cache, conditioning on the history through $A$.

## Depends on

- [Lyubashevsky's lattice identification protocol](lyubashevsky-identification.md)
- [Fiat–Shamir with aborts signatures](fiat-shamir-with-aborts-signatures.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
