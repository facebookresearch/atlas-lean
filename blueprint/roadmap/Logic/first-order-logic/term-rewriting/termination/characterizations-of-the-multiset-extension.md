# Characterizations of the multiset extension

Let $\succ$ be a strict partial ordering on a nonempty set $M$. On finite multisets over $M$ the following relations coincide with the [multiset extension](multiset-extension-of-an-ordering.md) $\succ_{\mathrm{mul}}$:

1. (Huet–Oppen) $S_1 \succ^{\mathrm{HO}}_{\mathrm{mul}} S_2$ iff $S_1 \ne S_2$ and, for every $m$ with $S_2(m) > S_1(m)$, there is $m' \succ m$ with $S_1(m') > S_2(m')$;
2. the [transitive closure](../abstract-reduction-system.md) of the one-step relation $\succ^1_{\mathrm{mul}}$, where $S_1 \succ^1_{\mathrm{mul}} S_2$ iff $S_2 = (S_1 - \{x\}) \cup Y$ for some $x \in S_1$ and multiset $Y$ all of whose elements are smaller than $x$.

For an arbitrary relation $\succ$ the three relations may differ.

## Depends on

- [Abstract reduction system](../abstract-reduction-system.md)
- [Multiset extension of an ordering](multiset-extension-of-an-ordering.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 1.4, the Huet/Oppen extension, the one-step extension and Theorem 1.11, pp. 9–10, with the proof of (a) referred to Baader and Nipkow, pp. 24–26.
