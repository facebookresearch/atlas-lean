# Maximin share allocations need not exist

Throughout, $N = \{1, \dots, n\}$ is a finite set of agents and $M$ a finite set of indivisible goods; agent $i$ has an additive valuation $v_i(S) = \sum_{g \in S} v_i(g)$ with $v_i(g) \ge 0$. For every $n \ge 3$ there are instances with $n$ agents, at most $3n + 4$ goods and additive valuations in which no complete allocation is MMS. With three agents there is an instance on nine goods in which every allocation gives some agent at most $\tfrac{39}{40}$ of her maximin share, and nine goods is the minimum for a negative example: for every $n$, every instance with $m \le n + 5$ goods admits an MMS allocation. For every $n \ge 4$ there are instances with at most $3n + 3$ goods in which every allocation gives some agent at most $1 - n^{-4}$ of her maximin share. For $n \le 2$ an MMS allocation always exists (cut and choose).

## Proof sketch

The constructions use valuations of the form $v_i(g_{rc}) = B + E_{rc} + \varepsilon_i(r, c)$ on goods arranged in a matrix: a large base value forces every maximin partition to use specific row/column triples, and small perturbations make the triples optimal for different agents incompatible. For the $39/40$ instance the impossibility is certified by checking all partitions into triples. Existence for $m \le n + 5$ is proved by a structural case analysis that repeatedly assigns a bundle to one agent and recurses on a smaller instance with the same maximin shares for the others.

## Depends on

- [Alpha-maximin share allocation](alpha-maximin-share-allocation.md)

## Sources

- D. Kurokawa, A. D. Procaccia, J. Wang, "Fair Enough: Guaranteeing Approximate Maximin Shares", Journal of the ACM 65(2) (2018); EC 2016.
- U. Feige, A. Sapir, L. Tauber, "A tight negative example for MMS fair allocations", WINE 2021, arXiv:2104.04977.
