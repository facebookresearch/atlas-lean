# Monogamy-of-entanglement property of coset states

Consider the game in which a challenger prepares a uniformly random coset state $|A_{s,s'}\rangle$ for a random subspace $A$ of dimension $n/2$ and sends it to an adversary $\mathcal{A}_0$, who outputs a bipartite state shared by non-communicating parties $\mathcal{A}_1,\mathcal{A}_2$; then both receive a description of $A$, and they win if $\mathcal{A}_1$ outputs an element of $A+s$ and $\mathcal{A}_2$ outputs an element of $A^{\perp}+s'$. Every (unbounded) strategy wins with probability at most $2^{-\Omega(n)}$ (information-theoretic version, with $\mathcal{A}_1,\mathcal{A}_2$ receiving $A$); a computational version holds when $\mathcal{A}_1,\mathcal{A}_2$ instead receive obfuscated membership programs for $A+s$ and $A^{\perp}+s'$, assuming iO and one-way functions.

## Proof sketch

For the information-theoretic statement, use the monogamy-of-entanglement framework: bound the operator norm of the sum of the products of the two winning projectors over the random choice of $(A,s,s')$, using the overlap structure of cosets (for two different subspaces the projectors are nearly orthogonal). The computational version reduces to it via subspace-hiding obfuscation and a sequence of hybrids replacing membership programs.

## Depends on

- [Coset states](coset-states.md)
- [Indistinguishability and virtual black-box obfuscation](../program-obfuscation/indistinguishability-and-virtual-black-box.md)

## Proof depends on

- [Monogamy-of-entanglement game for BB84 states](monogamy-bb84.md)

## Sources

- Andrea Coladangelo, Jiahui Liu, Qipeng Liu, Mark Zhandry, "Hidden Cosets and Applications to Unclonable Cryptography", CRYPTO (2021), IACR ePrint 2021/946.
