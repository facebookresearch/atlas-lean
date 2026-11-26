# Learning-augmented weighted paging

For weighted paging with cache size $k$ in which pages belong to $\ell$ distinct weight classes and the algorithm receives next-arrival predictions, if the predictions are perfect there is an $\ell$-competitive deterministic algorithm and an $O(\log \ell)$-competitive randomized algorithm, and both bounds are tight. With weights in $[1, W]$ this gives $O(\log W)$ and $O(\log \log W)$, versus the bounds $k$ and $O(\log k)$ without predictions; with imperfect predictions the ratios degrade smoothly to $O(k)$ and $O(\log k)$.

## Proof sketch

Bansal, Coester, Kumar, Purohit and Vee study the structure of Belady's rule restricted to each weight class and design a potential that couples the classes: within a class the algorithm follows the predicted order, and across classes it balances eviction budgets in a water-filling manner (deterministically) or through a fractional relaxation solved by entropic mirror descent and rounded online (randomized). Lower bounds embed $\ell$-point MTS-like adversaries in the weight classes.

## Depends on

- [Next-arrival predictions for paging](next-arrival-predictions.md)

## Proof depends on

- [Combining online algorithms for metrical task systems](combining-online-algorithms.md)

## Sources

- Nikhil Bansal, Christian Coester, Ravi Kumar, Manish Purohit, Erik Vee, "Learning-Augmented Weighted Paging", SODA (2022), arXiv:2011.09076.
