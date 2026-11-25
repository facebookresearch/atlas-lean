# Simulating a CRCW PRAM on an EREW PRAM

A $p$-processor priority CRCW PRAM can be simulated by a $p$-processor EREW PRAM with slowdown $\Theta(\log p)$: each CRCW step takes $O(\log p)$ EREW steps.

The upper bound follows from the [reduction of CRCW simulation to EREW sorting](reduction-of-crcw-simulation-to-erew-sorting.md), since $p$ keys can be sorted on a $p$-processor EREW PRAM in $O(\log p)$ time. The lower bound holds because the OR of $p$ bits takes one step on a CRCW PRAM but $\Omega(\log p)$ steps on an EREW PRAM, and the same holds for finding a maximum.

Priority is the strongest of the usual write-conflict rules, which are undefined, detecting, common, random and priority. So every CRCW variant among these is emulated by the EREW model with logarithmic slowdown.

## Depends on

- [Reduction of CRCW simulation to EREW sorting](reduction-of-crcw-simulation-to-erew-sorting.md)

## Sources

- B. Parhami, lecture slides for Part II, "Extreme Models", of *Introduction to Parallel Processing: Algorithms and Architectures* (Plenum Press, 1999), Fall 2008, Chapter 5: Theorem 5.1 (emulation of a priority CRCW PRAM by an EREW PRAM with slowdown $\Theta(\log p)$), the hierarchy EREW < CRCW-D < CRCW-C < CRCW-R < CRCW-P, and sorting in $O(\log p)$ time on the EREW PRAM.
- *Parallel algorithms*, lecture notes for 6.854 Advanced Algorithms, MIT, 2020, <https://courses.csail.mit.edu/6.854/20/Notes/n32-parallel.html>: CRCW computes OR in $O(1)$ time and maximum in constant time with $n^2$ processors, while EREW requires $\log n$ time for OR and for maximum, and CRCW$(k) \subseteq$ EREW$(k+1)$.
