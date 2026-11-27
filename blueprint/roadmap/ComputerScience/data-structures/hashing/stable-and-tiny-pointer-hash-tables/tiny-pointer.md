# Tiny pointers and dereference tables

A *dereference table* with load factor $1 - \delta$ manages an array of $n$ slots on behalf of keys from a universe $U$. The operation $\mathrm{Allocate}(k)$ either fails or returns a bit string $p$ (a *tiny pointer*) such that $\mathrm{Dereference}(k, p)$ returns a slot allocated exclusively to $k$; $\mathrm{Free}(k, p)$ releases it. Each key holds at most one live slot: after $\mathrm{Allocate}(k)$ returns $p$, $\mathrm{Free}(k, p)$ must be called before $\mathrm{Allocate}(k)$ is called again, and present keys are mapped to distinct slots. The value of $\mathrm{Dereference}(k, p)$ depends only on $k$, $p$ and the table's random bits, which are fixed when the table is created. At most $(1 - \delta) n$ slots are allocated at any time, and each allocation may fail with small probability. Because dereferencing is given the key $k$, a tiny pointer can be much shorter than the $\log_2 n$ bits of an ordinary index. Tiny pointers are *fixed-size* if all have the same length and *variable-size* if only their expected length is constrained.

## Depends on

- [Stable hash tables](stable-hash-table.md)

## Sources

- Michael A. Bender, Alex Conway, Martín Farach-Colton, William Kuszmaul, Guido Tagliavini, "Tiny Pointers", SODA (2023); ACM Transactions on Algorithms (2025), arXiv:2111.12800.
