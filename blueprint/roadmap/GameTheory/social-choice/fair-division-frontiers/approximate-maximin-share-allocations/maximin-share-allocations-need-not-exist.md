# Maximin share allocations need not exist

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every $n \ge 3$ there are instances with $n$ agents and additive valuations in which no complete allocation is MMS. With three agents there is an instance on nine goods in which every allocation gives some agent at most $\tfrac{39}{40}$ of her maximin share, and no instance with $m - n < 6$ (more precisely, with fewer than $n + 6$ goods) fails to admit an MMS allocation for $n = 3$; for every $n \ge 4$ there are instances in which every allocation gives some agent at most $1 - n^{-4}$ of her maximin share.

## Proof sketch

The constructions use valuations of the form $v_i(g_{rc}) = B + E_{rc} + \varepsilon_i(r, c)$ on goods arranged in a matrix: a large base value forces every maximin partition to use specific row/column triples, and small perturbations make the triples optimal for different agents incompatible. For the $39/40$ instance the impossibility is certified by checking all partitions into triples; the lower bound on the number of goods is proved by a structural case analysis.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Sources

- D. Kurokawa, A. D. Procaccia, J. Wang, "Fair Enough: Guaranteeing Approximate Maximin Shares", Journal of the ACM 65(2) (2018); EC 2016.
- U. Feige, A. Sapir, L. Tauber, "A tight negative example for MMS fair allocations", WINE 2021, arXiv:2104.04977.
