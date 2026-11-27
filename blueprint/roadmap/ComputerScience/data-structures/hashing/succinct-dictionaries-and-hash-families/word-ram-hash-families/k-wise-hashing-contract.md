# k-wise hashing contract for resamplable hash families

A *resamplable hash family* over keys $[U]$ and values $[m]$ supports $\mathrm{resample}$, which starts a new epoch with a fresh seed, and $\mathrm{eval}(u)$, which returns the current function's value at $u$. Its *$k$-wise contract* states: for every operation sequence fixed in advance in which each epoch evaluates at most $k$ distinct keys, the distribution of the transcript of returned values equals the ideal distribution in which, independently in each epoch, the distinct evaluated keys receive independent uniform values in $[m]$ (repeated keys repeating their value). The *$\delta$-approximate* contract only requires a coupling with the ideal transcript that fails with probability at most $E \delta$, where $E$ is the number of epochs. The contract restates the $k$-wise independence of Wegman and Carter for a hash family whose seed is redrawn at each epoch; the epoch and transcript formulation is not taken from the sources.

## Depends on

- [k-wise independent hash family](k-wise-independent-hash-family.md)
- [Oblivious-sequence specification of a randomized data structure](../../../data-structure-interfaces-and-refinement/oblivious-sequence-specification.md)

## Sources

- M. N. Wegman and J. L. Carter, "New Hash Functions and Their Use in Authentication and Set Equality", Journal of Computer and System Sciences 22(3), 1981.
- M. Thorup, "Simple Tabulation, Fast Expanders, Double Tabulation, and High Independence", Proceedings of the 54th IEEE Symposium on Foundations of Computer Science (FOCS), 2013; arXiv:1311.3121.
