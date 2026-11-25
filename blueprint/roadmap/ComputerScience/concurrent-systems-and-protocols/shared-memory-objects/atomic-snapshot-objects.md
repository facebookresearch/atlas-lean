# Atomic snapshot objects

An $n$-component atomic snapshot object supports, for each process $i$, the operation $\mathrm{update}_i(v)$, which sets component $i$ to $v$, and $\mathrm{scan}$, which returns the vector of all components. An implementation is correct if every history it produces is linearizable with respect to the sequential specification of an array in which scan returns the current contents of all components.

## Depends on

- [Linearizability](linearizability.md)

## Sources

- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
- Original definition and construction: Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt and N. Shavit, "Atomic snapshots of shared memory", *Journal of the ACM* 40(4):873–890, 1993. The formulation follows Aspnes, the chapter on atomic snapshots, which credits it to them.
