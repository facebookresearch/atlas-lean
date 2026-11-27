# Fixed dispatcher programs execute adaptive clients within certified budgets

Let a data structure be given by one fixed Word-RAM dispatcher program that, on an operation tag and arguments in designated registers, runs the method of that operation, together with an implementation certificate with charges $c(s, o)$ and potential $\Phi$. Then for every adaptive client admissible from the certificate's abstract initial state $s_0$, executing the client's operations one by one through the dispatcher (with argument delivery and result decoding by the caller) produces the client's specified answers, and the total number of instructions executed by the dispatcher is at most $\Phi(x_0) + \sum_j c(s_{j-1}, o_j)$, where $x_0$ is the certificate's initial machine state, which represents $s_0$. The bound is independent of the client's own (uncharged) control computation.

## Proof sketch

Induct on the client tree, starting from $\mathsf{rep}(s_0, x_0)$: at each call, admissibility of the client makes the operation admissible, and the representation relation gives a specified outcome and the certificate's per-operation inequality; summing over the run telescopes the potential.

## Depends on

- [Word-RAM implementation certificate with potential-amortized running time](word-ram-implementation-certificate.md)
- [State-transition specification of a data structure](state-transition-specification.md)

## Proof depends on

- [Potential method: amortized costs bound actual costs](../amortized-analysis/sum-cost-le-sum-amortized-cost.md)

## Sources

- T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, "Introduction to Algorithms", 3rd edition, MIT Press, 2009.
