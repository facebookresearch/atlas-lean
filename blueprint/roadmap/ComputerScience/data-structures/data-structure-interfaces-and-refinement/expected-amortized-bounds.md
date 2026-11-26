# Expected-amortized bounds with distribution invariants

Let a randomized implementation be run on an operation sequence $o_1, \dots, o_m$ fixed in advance, and let $\mu_j$ be the distribution of its state after $j$ operations. Suppose there are a potential $\Phi \ge 0$, charges $c_j$, and invariants $I_j$ on distributions (which may describe a seed law conditioned on the history, admissibility of the remaining operations and peak-space bounds) such that $I_0(\mu_0)$ holds and, whenever $I_{j-1}(\mu_{j-1})$, executing $o_j$ yields $\mu_j$ with $I_j(\mu_j)$ and

$$
\mathbb{E}_{\mu_{j-1}}[\mathrm{cost}(o_j)] + \mathbb{E}_{\mu_j}[\Phi] \le c_j + \mathbb{E}_{\mu_{j-1}}[\Phi].
$$

Then the expected total cost of the sequence is at most $\mathbb{E}_{\mu_0}[\Phi] + \sum_{j} c_j$.

## Proof sketch

Sum the per-step inequalities, telescope the expected potentials and drop the nonnegative final term. The invariant is carried along by induction on $j$.

## Depends on

- [Word-RAM implementation certificate with potential-amortized running time](word-ram-implementation-certificate.md)
- [Amortized cost of an operation](../amortized-analysis/amortized-cost.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
