# Composition of verified compilers

Let $\approx$ be a notion of [semantic preservation](notions-of-semantic-preservation.md) that is transitive, as all the notions of that page are. If [verified compilers](verified-compilers-and-verified-validators.md) $\mathrm{Comp}_1$ from $L_1$ to $L_2$ and $\mathrm{Comp}_2$ from $L_2$ to $L_3$ are given, then their monadic composition is a verified compiler from $L_1$ to $L_3$.

**Proof.** If the composition returns $\mathrm{OK}(C)$ on $S$, then $\mathrm{Comp}_1(S) = \mathrm{OK}(I)$ and $\mathrm{Comp}_2(I) = \mathrm{OK}(C)$ for some $I$, so $S \approx I$ and $I \approx C$, and $S \approx C$ by transitivity.

## Depends on

- [Verified compilers and verified validators](verified-compilers-and-verified-validators.md)
- [Notions of semantic preservation](notions-of-semantic-preservation.md)

## Sources

- X. Leroy, "A formally verified compiler back-end", *Journal of Automated Reasoning* 43(4):363–446, 2009, <https://xavierleroy.org/publi/compcert-backend.pdf>, Section 2.3, Theorem 2 and the remark that the properties of Section 2.1 are transitive.
