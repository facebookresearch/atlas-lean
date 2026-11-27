# Yao's 3/2 lower bound for online bin packing

No deterministic online bin-packing algorithm has asymptotic competitive ratio below $3/2$. Concretely, with capacity $41$ and item sizes $6$, $14$, $21$ (which admit the same $20$ feasible bin patterns as sizes $1/7 + \varepsilon$, $1/3 + \varepsilon$, $1/2 + \varepsilon$ with capacity $1$), consider the input consisting of $6m$ items of size $6$, followed by $6m$ of size $14$, followed by $6m$ of size $21$; the optima after the three phases are $m$, $3m$ and $6m$. For every online algorithm $A$ and every $m$, after one of the three phases $A$ uses at least $\frac32$ times the optimum of that prefix. A two-phase variant gives the bound $4/3$ for two item types.

## Proof sketch

Weight bins by which phases' items they contain; a linear-programming duality argument over the $20$ bin patterns shows that the three ratios cannot all be below $3/2$, because the algorithm cannot revise bins opened in earlier phases.

## Depends on

- [Deterministic online bin packing algorithms](online-bin-packing-model.md)

## Sources

- A. C.-C. Yao, "New Algorithms for Bin Packing", Journal of the ACM 27(2), 1980.
- J. Balogh, J. Békési, G. Dósa, L. Epstein and A. Levin, "A New and Improved Algorithm for Online Bin Packing", 26th European Symposium on Algorithms (ESA), 2018.
