# Distance accumulates additively along probabilistic loops

Let $K_1, \dots, K_t$ and $K'_1, \dots, K'_t$ be Markov kernels (probabilistic loop bodies) with $\sup_x \Delta(K_i(x), K'_i(x)) \le \varepsilon_i$. Then for every initial distribution $\mu$,

$$\Delta\bigl(\mu K_1 \cdots K_t,\ \mu K'_1 \cdots K'_t\bigr) \le \sum_{i=1}^{t}\varepsilon_i.$$

In particular a bounded adaptive probabilistic iteration whose body is replaced by an $\varepsilon$-close body changes its output law by at most $t\varepsilon$.

## Proof sketch

Telescoping: replace the kernels one at a time; each replacement costs at most $\varepsilon_i$ because Markov kernels contract statistical distance.

## Depends on

- [Total variation distance between finite measures](../../../Probability/convergence-of-measures/total-variation-distance/total-variation-dist.md)

## Sources

- S. P. Vadhan, "Pseudorandomness", Foundations and Trends in Theoretical Computer Science 7(1-3), 2012.
