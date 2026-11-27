# Self-healing returns the dictionary to the fast mode

In the with-high-probability succinct dictionary, if the seed is good on the trailing window of $2q + 2$ operations before an operation $o$ (where $q$ is the epoch length), then within at most $q$ operations after the window starts either a self-healing conversion from the fallback CSR representation or an epoch rollover places the dictionary in the clean fast state, and it stays there through $o$; in the clean fast state no capacity, pool, buffer or rollover guard of the fast path fires, so $o$ runs on the fast path in $O_c(1)$ instructions.

## Proof sketch

In a clean epoch the background work is bounded by a potential that decreases with each tick and stays below the epoch length on good seeds, so the rollover never aborts; the buffer grows by at most the number of colliding insertions, which is small on good seeds. A self-healing attempt succeeds as soon as the checker certifies the seed good on the current state.

## Depends on

- [Compressed sparse row fallback dictionary](compressed-sparse-row-fallback.md)
- [Deamortized global rebuilding by epochs](deamortized-global-rebuilding.md)

## Proof depends on

- [Good hash seeds on a trailing window of operations](good-seeds-on-a-trailing-window.md)
- [In-place slot rearrangement by cycle following](in-place-slot-rearrangement.md)

## Sources

- M. A. Bender, M. Farach-Colton, J. Kuszmaul and W. Kuszmaul, "Modern Hashing Made Simple", Proceedings of the 2024 SIAM Symposium on Simplicity in Algorithms (SOSA), 2024.
- M. H. Overmars, "The Design of Dynamic Data Structures", Lecture Notes in Computer Science 156, Springer, 1983.
