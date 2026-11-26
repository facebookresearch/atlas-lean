# Fresh Lyubashevsky commitments rarely hit a random-oracle cache

Let $q$ be prime, let $\gamma$ be a positive integer with $2\gamma < q$, let $A \in \mathbb{Z}_q^{n\times m}$ be uniform, and let a history depending on $A$ choose a cache $\mathcal{C}$ of at most $Q$ commitment values before a fresh mask $y$ is drawn uniformly from $[-\gamma, \gamma]^m$, independently of the history given $A$. Then

$$
\Pr\bigl[A y \in \mathcal{C}\bigr] \le Q\,\Bigl(\Bigl(\tfrac{4\gamma + 1}{2\gamma + 1}\Bigr)^{m} q^{-n} + (2\gamma + 1)^{-m}\Bigr) =: B_\gamma,
$$

averaged over $A$, including attempts whose response later aborts. With $0 < \beta \le \gamma$, the published commitment $A z - T c$ of the public simulator, which outputs $z$ uniform on the inner box $[-(\gamma - \beta), \gamma - \beta]^m$ with probability equal to the exact acceptance factor $p = ((2(\gamma-\beta)+1)/(2\gamma+1))^m$, hits the cache with probability at most $p\,B_{\gamma - \beta}$. Hence replacing every hash read of the all-attempt signer by fresh programming changes the joint law of signatures and cache by at most $K q_S\,B_\gamma$ in statistical distance.

## Proof sketch

Fix $A$. Every fibre $\{y \in [-\gamma,\gamma]^m : A y = c\}$ injects, by $y \mapsto y - y_0$ for one fixed element $y_0$, into $\ker A \cap [-2\gamma, 2\gamma]^m$, so each cached value is hit with probability at most $|\ker A \cap [-2\gamma, 2\gamma]^m| / (2\gamma+1)^m$, whatever the cache. A nonzero integer vector in $[-2\gamma, 2\gamma]^m$ is nonzero modulo $q$ because $2\gamma < q$, so it lies in $\ker A$ with probability $q^{-n}$ over uniform $A$; hence the expected kernel count is at most $1 + (4\gamma+1)^m q^{-n}$. A union bound over the $Q$ cached values and averaging over $A$ give $B_\gamma$. The same argument on the inner box gives $B_{\gamma-\beta}$, since $z \mapsto A z - T c$ is a translate of $z \mapsto A z$.

## Depends on

- [Lyubashevsky's lattice identification protocol](lyubashevsky-identification.md)
- [Fiat–Shamir with aborts signatures](fiat-shamir-with-aborts-signatures.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Cryptology ePrint Archive, Paper 2023/246, 2023.
