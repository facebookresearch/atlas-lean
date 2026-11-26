# The multiset extension preserves well-foundedness

If $\succ$ is a well-founded strict partial ordering on a set $M$, then its [multiset extension](multiset-extension-of-an-ordering.md) $\succ_{\mathrm{mul}}$ is a well-founded strict partial ordering on the finite multisets over $M$ (Dershowitz–Manna).

**Proof idea.** Arrange a descending chain $S_1 \succ_{\mathrm{mul}} S_2 \succ_{\mathrm{mul}} \cdots$ in a finitely branching tree: a new root has the elements of $S_1$ as children, and each element added at step $i$ becomes a child of a removed element larger than it. An infinite chain gives an infinite tree, which by König's lemma has an infinite path, a descending chain in $M$.

## Depends on

- [Multiset extension of an ordering](multiset-extension-of-an-ordering.md)

## Proof depends on

- [The multiset extension of a strict order is a strict order](the-multiset-extension-of-a-strict-order-is-a-strict-order.md)

## Sources

- U. Waldmann, *Automated Reasoning*, lecture notes, Max Planck Institute for Informatics, winter semester 2019/20, <https://rg1-teaching.mpi-inf.mpg.de/autrea-ws19/script.pdf>, Section 1.4, Lemma 1.9 (König's lemma) and Theorem 1.10 (c), p. 9, with the proof referred to Baader and Nipkow, pp. 22–24.
