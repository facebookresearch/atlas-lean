# Monotone access structures and secret-sharing schemes

Let $\mathcal{P}$ be a finite set of parties. A *monotone access structure* is an upward-closed family $\mathcal{A}$ of subsets of $\mathcal{P}$ (the *authorized* coalitions); examples are the threshold structure $\{S : |S| \ge t\}$, the all-party structure, upward closures of given sets, preimages under share assignments, intersections, unions and duals. Every authorized coalition contains a minimal authorized one, and subsets of unauthorized coalitions are unauthorized. A *secret-sharing scheme* for $\mathcal{A}$ with secret space $Z$ consists of a share map $\mathrm{share}(z, \kappa) = (\sigma_P)_{P \in \mathcal{P}}$ from a secret and a key $\kappa$, reconstruction maps for authorized coalitions, and a class $\mathcal{K}$ of allowed key distributions. It is *perfectly correct* if every authorized coalition reconstructs $z$ from its shares for every key, and *perfectly private* if, for every key distribution in $\mathcal{K}$ and every unauthorized coalition $S$, the distribution of $(\sigma_P)_{P \in S}$ is the same for all secrets; it is *$\delta$-statistically private* if these distributions are within statistical distance $\delta$. The standard choice of $\mathcal{K}$ is the class of *translation-invariant* key distributions on an additive group (containing the uniform distribution).

## Sources

- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
- Divesh Aggarwal, "Secret Sharing Despite Non-Extractable Randomness", arXiv:2610.20173v2, 2026.
- Adi Shamir, "How to Share a Secret", Communications of the ACM, 1979.
