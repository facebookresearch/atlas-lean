# Fresh Lyubashevsky commitments rarely hit a random-oracle cache

Let $q$ be prime, let $A \in \mathbb{Z}_q^{n\times m}$ be uniform, and let a history depending on $A$ choose a cache $\mathcal{C}$ of at most $Q$ commitment values before a fresh mask $y$ is drawn uniformly from $[-\gamma, \gamma]^m$, independently of the history given $A$. Let

$$
\varepsilon_\gamma = \mathbb{E}_A\Bigl[\max_{w} \Pr_{y}\bigl[A y = w\bigr]\Bigr]
$$

be the average guessing probability of the commitment. Then $\Pr[A y \in \mathcal{C}] \le Q\,\varepsilon_\gamma$, averaged over $A$, including attempts whose response later aborts. This bounds the bad event of the hybrid argument of Barbosa et al. (proof of Theorem 3), in which the hash reads of the signing attempts are replaced one at a time by fresh programming; summing over the attempts of all signing queries gives the reprogramming term of their Theorem 3, stated in terms of this guessing probability.

## Proof sketch

Fix $A$ and the history. The cache is fixed before $y$ is drawn, so a union bound over its at most $Q$ values bounds the hit probability by $Q \max_w \Pr_y[A y = w]$; averaging over $A$ gives $Q\,\varepsilon_\gamma$. The same union bound applies to the public simulator. With $0 < \beta \le \gamma$, it outputs $z$ uniform on the inner box $[-(\gamma - \beta), \gamma - \beta]^m$ with probability equal to the exact acceptance factor $p = ((2(\gamma-\beta)+1)/(2\gamma+1))^m$, and its published commitment $A z - T c$ hits the cache with probability at most $p\,Q\,\varepsilon_{\gamma - \beta}$: the commitment is a translate of $z \mapsto A z$ by $T c$, with $c$ independent of $z$, so its largest atom probability is at most that of $A z$; it is published only with probability $p$, which gives $p\,Q\,\varepsilon_{\gamma-\beta}$.

## Depends on

- [Lyubashevsky's lattice identification protocol](lyubashevsky-identification.md)
- [Fiat–Shamir with aborts signatures](fiat-shamir-with-aborts-signatures.md)

## Sources

- Vadim Lyubashevsky, "Lattice Signatures without Trapdoors", Advances in Cryptology – EUROCRYPT 2012, 2012.
- Manuel Barbosa et al., "Fixing and Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium", Advances in Cryptology – CRYPTO 2023, 2023; full version Cryptology ePrint Archive, Paper 2023/246, Eq. (1) (guessing probability of the commitment), Section 3 (the bad event that a fresh commitment hits an earlier hash query) and Theorem 3.
