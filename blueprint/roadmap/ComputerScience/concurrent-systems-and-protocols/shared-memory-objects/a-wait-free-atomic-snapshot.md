# A wait-free atomic snapshot

In the snapshot algorithm of Afek, Attiya, Dolev, Gafni, Merritt and Shavit for $n$ processes, each update first performs a scan and writes its value together with that embedded scan and a sequence number; a scan repeatedly collects all components and returns either two identical consecutive collects or, if it observes some process move twice, the scan embedded in that process's second update. The resulting snapshot object is linearizable, and it is wait-free: every scan finishes within $O(n)$ collects.

## Depends on

- [Progress conditions for concurrent implementations](progress-conditions-for-concurrent.md)

## Proof depends on

- [The double-collect lemma](the-double-collect-lemma.md)

## Sources

- Original construction: Y. Afek, H. Attiya, D. Dolev, E. Gafni, M. Merritt and N. Shavit, "Atomic snapshots of shared memory", *Journal of the ACM* 40(4):873–890, 1993. The formulation follows Aspnes, the chapter on atomic snapshots (snapshots using double collects with helping), which credits it to them.
- J. Aspnes, *Notes on Theory of Distributed Systems*, Yale University, 2020, <https://arxiv.org/abs/2001.04235>
