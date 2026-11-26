# Next Fit and First Fit

**Next Fit** keeps a single open bin: an item goes into it if it fits, otherwise the bin is closed and a new bin is opened with the item. **First Fit** keeps all bins open and places each item into the first bin with enough room, opening a new last bin if none has room. Both process items in input order and return packings.

## Depends on

- [Packings and the volume bound](packings-and-volume-bound.md)

## Sources

- D. S. Johnson, "Near-Optimal Bin Packing Algorithms", PhD thesis, Massachusetts Institute of Technology, 1973.
- D. P. Williamson and D. B. Shmoys, "The Design of Approximation Algorithms", Cambridge University Press, 2011.
