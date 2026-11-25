# Paged address translation

In this abstract model, one address space uses natural-number byte addresses. Pages and frames
have size $B=2^s$ bytes, with $s$ a natural number. A virtual address $a$ has virtual page number
$v=\lfloor a/B\rfloor$ and offset $o=a\bmod B$, so $a=vB+o$ and $0\le o<B$.

A linear page table has a base address and a positive entry size in bytes. The slot for page $v$
is at the base plus $v$ times the entry size. Each slot gives an entry with a physical frame number
(PFN), permissions for reading, writing and executing, and valid and present bits. Unused pages
have invalid entries. The table walk checks these conditions in order:

1. An invalid entry gives an invalid-page fault.
2. Otherwise, a disallowed access gives a protection fault.
3. Otherwise, a nonresident page gives a page fault.
4. Otherwise, the walk returns the entry's frame and permissions. The translated byte address is
   $\mathrm{PFN}\cdot B+o$; its frame is $\mathrm{PFN}$ and its offset is $o$.

A translation-lookaside buffer (TLB) is modeled as a partial map from virtual page numbers to
frames and permissions. On a hit, translation checks the cached permissions and either returns
the address using the cached frame or reports a protection fault, without walking the table. On a
miss, it walks the table and adds the mapping only if the walk succeeds. This combines refill and
translation in one abstract step; it does not model memory effects, eviction or address-width limits.

If each cached frame and its permissions match a valid, resident entry in the same table,
translation gives the same outcome as an uncached walk and preserves this agreement. Any fault
leaves the cache unchanged. A success records the walk's mapping for the requested page, which
leaves the cache unchanged on a hit, and preserves the original byte offset in the physical frame.

## Sources

- R. H. Arpaci-Dusseau and A. C. Arpaci-Dusseau, *Operating Systems: Three Easy Pieces*, version 1.10:
    - Chapter 18, "Paging: Introduction", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-paging.pdf>: the VPN and offset split, the linear table lookup and the validity and permission checks (Figure 18.6), and the present bit (§18.3). The model combines these by checking presence after permission.
    - Chapter 19, "Paging: Faster Translations (TLBs)", <https://pages.cs.wisc.edu/~remzi/OSTEP/vm-tlbs.pdf>: the TLB hit and miss control flow, including the permission check on a hit (Figure 19.1). The model combines a successful refill and translation rather than retrying an instruction.
