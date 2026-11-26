# c3-LTCs of every rate below one

For every $\rho < 1$ there is a $c^3$-LTC family of binary linear codes with rate at least $\rho$, constant relative distance, constant locality and constant soundness. The family can be obtained from the left-right Cayley complex codes by distance amplification (expander-based concatenation) followed by the Alon-Edmonds-Luby / Kopparty-Meir-Ron-Zewi-Saraf rate-boosting transformation, both of which preserve constant locality and soundness.

## Proof sketch

Start from a $c^3$-LTC of some positive rate. Distance amplification along a bipartite expander turns relative distance $\delta$ into relative distance close to $1 - \rho$ for a target outer rate while multiplying locality by a constant. The rate-boosting transformation then concatenates many copies in an expander-based layout so that the overall rate approaches $\rho$ and the tester simulates the base tester on random views.

## Depends on

- [Dinur–Evra–Livne–Lubotzky–Mozes: explicit c3-LTCs from left-right Cayley complexes](dellm-c3-ltc-theorem.md)
- [Good locally testable codes of every rate below one](../locally-testable-codes/theorem-1-2.md)

## Proof depends on

- [Dinur–Evra–Livne–Lubotzky–Mozes: explicit c3-LTCs from left-right Cayley complexes](dellm-c3-ltc-theorem.md)
- [Good locally testable codes of every rate below one](../locally-testable-codes/theorem-1-2.md)

## Sources

- I. Dinur, S. Evra, R. Livne, A. Lubotzky, S. Mozes, "Locally testable codes with constant rate, distance, and locality", STOC (2022), arXiv:2111.04808.
- P. Panteleev, G. Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022), arXiv:2111.03654.
