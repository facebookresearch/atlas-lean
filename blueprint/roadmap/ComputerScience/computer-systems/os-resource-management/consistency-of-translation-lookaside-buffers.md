# Consistency of translation lookaside buffers under shootdown

Consider [paged address translation](paged-address-translation.md) on a machine with several cores. Each core has a *translation lookaside buffer* (TLB) caching entries $(\mathit{asid}, \mathit{vpn}) \mapsto (\mathit{pfn}, \mathit{prot})$:
- a TLB hit returns the cached entry;
- a miss walks the current page table of the running address space and caches the result.

Assume two disciplines:
1. **Shootdown.** A change to the page-table entry for $(\mathit{asid}, \mathit{vpn})$ and the invalidation of every TLB entry for $(\mathit{asid}, \mathit{vpn})$ on every core take effect together as one step: no core translates that page between the start of the change and the completion of the invalidations, as when the other cores are stalled during the shootdown.
2. **Address-space separation.** Entries are tagged with the address-space identifier of the process they came from and are used only for that identifier. Without tags, the TLB is flushed whenever the page-table base register changes on a context switch.

**Theorem.** At every moment, every valid TLB entry on every core agrees with the current page table of its address space. Consequently, every translation served from a TLB equals the translation the page table alone would give. Translation with TLBs refines translation by the page table.

**Proof.** The statement is an invariant on the TLB contents and the page tables, and each kind of step preserves it:
- a miss caches the current page-table entry;
- a hit changes nothing;
- a page-table update removes every possibly stale entry for that page before taking effect, by shootdown;
- a context switch either starts with an empty TLB or, with tags, only ever uses entries tagged with the running address space.

Initially the TLBs are empty.

Both disciplines are needed. Without shootdown, a core may keep using a translation to a frame that has been reassigned. Without tags or flushes, the virtual page 10 of process $P_1$, mapped to frame 100, and the same virtual page of $P_2$, mapped to frame 170, are indistinguishable in the TLB.

## Depends on

- [Paged address translation](paged-address-translation.md)

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, version 1.10, Arpaci-Dusseau Books, chapter 19 "Paging: Faster Translations (TLBs)", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-tlbs.pdf>: the TLB as a cache of virtual-to-physical translations with valid and protection bits, TLB miss handling by walking the page table, and Section 19.5 (context switches: flushing the TLB when the page-table base register changes, or address space identifiers, with the example of virtual page 10 mapped to frames 100 and 170). The invariant and its proof are written out here.
