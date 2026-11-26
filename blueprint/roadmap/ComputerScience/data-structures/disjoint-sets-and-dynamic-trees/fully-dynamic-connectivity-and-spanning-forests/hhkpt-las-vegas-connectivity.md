# Las Vegas fully dynamic connectivity in O(log n (log log n)^2) amortized expected time

There is a Las Vegas randomized fully dynamic connectivity data structure on $n$ vertices with $O(\log n (\log \log n)^2)$ amortized expected update time and $O(\log n / \log \log \log n)$ worst-case query time. The structure maintains a public spanning forest $F$ as connectivity witness, so the guarantees hold even when the update sequence depends on $F$.

## Proof sketch

The level hierarchy of Holm, de Lichtenberg and Thorup is kept, but replacement edges are found by random sampling of non-tree edges at a level, in the style of Henzinger and King and of Thorup, so that most levels are resolved by a few samples. The sampling is made Las Vegas by verifying candidates, and a refined, approximately balanced hierarchy reduces the number of levels touched per deletion. The bound nearly matches the cell-probe lower bound of Patrascu and Demaine.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)

## Proof depends on

- [Replacement edges after deleting a spanning-forest edge](replacement-edge-lemma.md)
- [Holm-de Lichtenberg-Thorup: deterministic polylogarithmic amortized connectivity and MSF](hdt-amortized-connectivity.md)

## Sources

- Shang-En Huang, Dawei Huang, Tsvi Kopelowitz, Seth Pettie, Mikkel Thorup, "Fully Dynamic Connectivity in O(log n (log log n)^2) Amortized Expected Time", SODA (2017); TheoretiCS (2023), arXiv:1609.05867.
- Monika R. Henzinger, Valerie King, "Randomized fully dynamic graph algorithms with polylogarithmic time per operation", J. ACM 46(4) (1999).
