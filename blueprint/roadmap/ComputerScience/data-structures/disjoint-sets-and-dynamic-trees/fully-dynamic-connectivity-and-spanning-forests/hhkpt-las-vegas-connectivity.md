# Las Vegas fully dynamic connectivity in O(log n (log log n)^2) amortized expected time

There is a Las Vegas randomized fully dynamic connectivity data structure on $n$ vertices with $O(\log n (\log \log n)^2)$ amortized expected update time and $O(\log n / \log \log \log n)$ worst-case query time. The structure maintains a public spanning forest $F$ as connectivity witness, so the guarantees hold even when the update sequence depends on $F$.

## Proof sketch

The structure keeps a Holm–de Lichtenberg–Thorup style hierarchy: edges have depths, the witness forest is a maximum spanning forest with respect to depth, and components at depth $i$ have at most $n/2^i$ vertices. After an $i$-witness edge is deleted, the replacement search distinguishes two situations. If a constant fraction of the $i$-non-witness endpoints touching the smaller side belong to replacement edges, a two-stage batch sampling test in the style of Henzinger and Thorup finds one with $O(1)$ expected samples, each checked exactly. Otherwise all those endpoints are enumerated and marked: an edge marked once is a replacement edge and an edge marked twice is promoted to depth $i+1$, so a constant fraction of the enumerated edges is promoted and pays for the enumeration. Splitting non-witness endpoints into primary ones, which are sampled, and secondary ones keeps the sampling structure cheap to update, at $O((\log\log n)^2)$ per promotion. Since Pătraşcu and Demaine show that $O(\log n (\log\log n)^2)$ update time forces $\Omega(\log n/\log\log\log n)$ query time, both bounds are within $(\log\log n)^{O(1)}$ factors of optimal.

## Depends on

- [Oblivious and adaptive adversaries; amortized and worst-case update time](adversary-and-update-time-models.md)
- [Fully dynamic connectivity, spanning forest and minimum spanning forest problems](fully-dynamic-connectivity-problems.md)

## Proof depends on

- [Replacement edges after deleting a spanning-forest edge](replacement-edge-lemma.md)
- [Holm-de Lichtenberg-Thorup: deterministic polylogarithmic amortized connectivity and MSF](hdt-amortized-connectivity.md)

## Sources

- Shang-En Huang, Dawei Huang, Tsvi Kopelowitz, Seth Pettie, Mikkel Thorup, "Fully Dynamic Connectivity in O(log n (log log n)^2) Amortized Expected Time", TheoretiCS (2023), arXiv:1609.05867; full version of the extended abstracts by Thorup (STOC 2000) and by Huang, Huang, Kopelowitz and Pettie (SODA 2017).
- Monika R. Henzinger, Valerie King, "Randomized fully dynamic graph algorithms with polylogarithmic time per operation", J. ACM 46(4) (1999).
