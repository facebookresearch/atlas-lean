# Las Vegas dynamic minimum spanning forest with n^{o(1)} worst-case update time

There is a Las Vegas randomized algorithm maintaining a minimum spanning forest of an $n$-vertex graph under edge insertions and deletions with $O(n^{o(1)})$ worst-case update time with high probability. Combined with the expander decomposition and pruning algorithm of Saranurak and Wang, the update time is $n^{O(\sqrt{\log \log n / \log n})}$, both in expectation and with high probability.

## Proof sketch

The framework common to Wulff-Nilsen and to Nanongkai and Saranurak is: decompose into expanders, maintain each expander under deletions by pruning, and handle the inter-cluster edges by recursion. Pruning is improved to subpolynomial cost per deletion, and the minimum spanning forest of the recursion's graphs, which have at most $(1 + o(1)) n$ edges, is maintained by the contraction technique of Henzinger-King and Holm-de Lichtenberg-Thorup instead of topology trees. With $O(\sqrt{\log n / \log \log n})$ recursion levels the cost is $n^{o(1)}$.

## Depends on

- [Nanongkai-Saranurak: adaptive Las Vegas dynamic spanning forest in O(n^0.49306) worst-case time](ns-adaptive-spanning-forest.md)
- [Saranurak-Wang expander pruning under online edge deletions](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/expander-pruning-theorem.md)
- [Saranurak-Wang near-linear-time strong expander decomposition](../../../../GraphTheory/graph-families-and-operations/expander-decomposition-and-pruning/saranurak-wang-expander-decomposition.md)

## Proof depends on

- [Holm-de Lichtenberg-Thorup: deterministic polylogarithmic amortized connectivity and MSF](hdt-amortized-connectivity.md)

## Sources

- Danupon Nanongkai, Thatchaphol Saranurak, Christian Wulff-Nilsen, "Dynamic Minimum Spanning Forest with Subpolynomial Worst-case Update Time", FOCS (2017), arXiv:1708.03962.
- Christian Wulff-Nilsen, "Fully-Dynamic Minimum Spanning Forest with Improved Worst-Case Update Time", STOC (2017), arXiv:1611.02864.
- Thatchaphol Saranurak, Di Wang, "Expander Decomposition and Pruning: Faster, Stronger, and Simpler", SODA (2019), arXiv:1812.08958.
