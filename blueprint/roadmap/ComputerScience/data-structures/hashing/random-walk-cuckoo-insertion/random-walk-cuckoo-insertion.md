# Random-walk insertion for d-ary cuckoo hashing

*Random-walk insertion*, introduced by Fotakis, Pagh, Sanders and Spirakis, inserts a new key $x_1$ by a chain of evictions: a key $x_t$ is placed into one of its candidate slots chosen at random; if that slot held a key $x_{t+1}$, then $x_{t+1}$ is evicted and placed by the same rule, until a key is placed into an empty slot. The *insertion time* is the number of placements performed. The analyses differ in how the slot is chosen:

- (a) *Uniform walk* (Bell and Frieze, Section I): each key $x_t$, the new key included, takes $h_{i_t}(x_t)$ for a fresh uniform $i_t \in [d]$, without inspecting its other candidates first; so the new key may evict even when another of its candidates is free, and an evicted key may choose the slot it was just evicted from.
- (b) *Walk without immediate return* (Walzer, Section 1, Figure 1): the new key takes a uniform one of its $d$ candidates without inspecting the others; an evicted key takes a uniform one of its other $d - 1$ candidates, excluding the slot it was just evicted from.
- (c) *Free-slot-first walk*: a key takes a free candidate slot if one exists, and otherwise a uniform candidate.

The bounds cited for these variants are stated for (a) and (b); they are not claimed here for (c).

## Depends on

- [d-ary cuckoo hashing and its hashing graph](d-ary-cuckoo-hashing.md)

## Sources

- Dimitris Fotakis, Rasmus Pagh, Peter Sanders, Paul Spirakis, "Space Efficient Hash Tables with Worst Case Constant Access Time", Theory of Computing Systems 38(2) (2005).
- Tolson Bell, Alan Frieze, "O(1) Insertion for Random Walk d-ary Cuckoo Hashing up to the Load Threshold", FOCS (2024), arXiv:2401.14394.
- Stefan Walzer, "Insertion Time of Random Walk Cuckoo Hashing below the Peeling Threshold", ESA (2022), arXiv:2202.05546.
