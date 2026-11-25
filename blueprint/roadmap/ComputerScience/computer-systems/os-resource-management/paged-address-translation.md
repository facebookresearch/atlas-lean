# Paged address translation

In paging, the virtual address space of a process and physical memory are divided into fixed-size pages and page frames of $2^s$ bytes.

- **Address split.** A virtual address splits into a *virtual page number* (VPN), its high-order bits, and an *offset* of $s$ bits within the page.
- **Page table.** A per-process *page table* maps virtual page numbers to *page-table entries* (PTEs). A PTE holds a *physical frame number* (PFN), a *valid bit* marking whether the page is in use, *protection bits* stating whether the page may be read, written or executed, and further bits such as a present bit.
- **Translation.** To translate a virtual address with VPN $v$ and offset $o$, the hardware fetches the PTE for $v$, at the page-table base address plus $v$ times the PTE size for a linear page table:
    - if the PTE is not valid, the access raises a segmentation fault;
    - otherwise, if the protection bits forbid the access, it raises a protection fault;
    - otherwise, if the present bit is clear because the page is not resident in physical memory, it raises a page fault;
    - otherwise the physical address is the PFN followed by the offset, $\mathrm{PFN} \cdot 2^s + o$.
- **Translation-lookaside buffer.** A *translation-lookaside buffer* (TLB) is a hardware cache of virtual-to-physical translations in the memory-management unit, consulted before the page table:
    - on a TLB hit with permitted access, the physical address is formed from the cached PFN;
    - on a hit with forbidden access, a protection fault is raised;
    - on a miss, the page table is consulted as above and the translation is inserted into the TLB.

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, version 1.10:
    - Chapter 18, "Paging: Introduction", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-paging.pdf>: the VPN and offset split, page-table entries with valid, protection and present bits, and the translation procedure with segmentation and protection faults (Figure 18.6).
    - Chapter 19, "Paging: Faster Translations (TLBs)", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-tlbs.pdf>: the TLB and the TLB control-flow algorithm (Figure 19.1).
