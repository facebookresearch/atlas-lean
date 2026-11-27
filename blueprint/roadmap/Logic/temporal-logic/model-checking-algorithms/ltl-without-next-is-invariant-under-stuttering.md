# LTL without next is invariant under stuttering

Two infinite words over $2^{AP}$ are *stutter equivalent* if they become equal after collapsing every maximal block of consecutive equal letters to a single letter (blocks may be finite, and a word that is eventually constant ends with an infinite block). If $\sigma$ and $\sigma'$ are stutter equivalent, then they satisfy the same LTL formulas that do not use the next operator $\mathbf{X}$.

## Depends on

- [Satisfaction of LTL formulas on ω-words](../linear-temporal-logic/satisfies.md)

## Sources

- C. Baier and J.-P. Katoen, *Principles of Model Checking*, MIT Press, 2008, Section 7.7
- J.-P. Katoen, *Model Checking*, Lecture 17: Partial-order reduction, RWTH Aachen University, 2019, "Stutter equivalence", <https://moves.rwth-aachen.de/wp-content/uploads/WS1920/MC/mc2019_handout_lec17.pdf>
- A. Kučera and J. Strejček, "The stuttering principle revisited: on the expressiveness of nested X and U operators in the logic LTL", *CSL 2002*, LNCS 2471, Springer, 2002, Section 2, <https://www.fi.muni.cz/usr/kucera/papers/csl02.pdf>
- L. Lamport, "What good is temporal logic?", *Information Processing 83*, North-Holland, 1983
