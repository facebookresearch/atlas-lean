# k-wise hashing contract for resamplable hash families

A *resamplable hash family* over keys $[U]$ and values $[m]$ supports $\mathrm{resample}$, which starts a new epoch with a fresh seed, and $\mathrm{eval}(u)$, which returns the current function's value at $u$. Its *$k$-wise contract* states: for every operation sequence fixed in advance in which each epoch evaluates at most $k$ distinct keys, the distribution of the transcript of returned values equals the ideal distribution in which, independently in each epoch, the distinct evaluated keys receive independent uniform values in $[m]$ (repeated keys repeating their value). The *$\delta$-approximate* contract only requires a coupling with the ideal transcript that fails with probability at most $E \delta$, where $E$ is the number of epochs.

## Depends on

- [k-wise independent hash family](k-wise-independent-hash-family.md)
- [Oblivious-sequence specification of a randomized data structure](../../../data-structure-interfaces-and-refinement/oblivious-sequence-specification.md)

## Sources

- J. L. Carter and M. N. Wegman, "Universal Classes of Hash Functions", Journal of Computer and System Sciences 18(2), 1979.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
