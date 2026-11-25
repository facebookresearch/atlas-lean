# Randomized streaming algorithm with $s$ bits of memory

A one-pass algorithm over an alphabet $\alpha$ whose state is one of $2^s$ memory contents, given by
an initial state, a transition reading one stream element, and a real output, all depending on a
random seed $r$ drawn uniformly from a finite nonempty set $R$. This is the model of the source,
Section 1, with one difference: the seed is not counted in the memory. That is the standard
public-randomness (random-oracle) streaming model.

The source's algorithms keep their random bits in memory or draw them during the pass, so they are
special cases with the same memory. A space lower bound in this model is therefore at least as
strong as the source's. The source's two lower bounds remain true in it, because their proofs use
the seed only as the public coin of a communication protocol:

- [Proposition 3.1](space-lower-bound-max-freq.md): Alice and Bob share $r$. Alice runs the
  algorithm on the elements of $x$ and sends the $s$-bit memory content; Bob finishes the run on
  $y$. This is a one-way public-coin protocol for disjointness of cost $s + O(1)$, and the
  disjointness lower bound holds for public-coin protocols.
- [Theorem 3.2](space-lower-bound-freq-moment.md): the multiparty bound (Proposition 3.3) is proved
  against a fixed input distribution. After amplifying by independent copies (seed space $R^k$,
  memory $ks$ bits, still an algorithm of this model) and averaging the error over that
  distribution, one seed can be fixed. That gives a deterministic protocol, so the size of $R$
  never enters.

## Sources

- N. Alon, Y. Matias and M. Szegedy, "The space complexity of approximating the frequency moments", *J. Comput. System Sci.* 58 (1999) 137–147, Section 1 (model) and Section 3 (lower bounds; p. 11 for the distributional method).
