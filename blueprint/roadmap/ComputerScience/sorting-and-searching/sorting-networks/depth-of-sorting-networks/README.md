# Depth of sorting networks

## Levels

- [Comparator levels under earliest scheduling](levels.md)
- [Depth bound for a comparator list](depth-le.md)
- [Depth of sequential composition of comparator lists](append.md)
- [Comparators inside a block leave levels outside it unchanged](levels-of-not-mem.md)
- [Levels inside a block depend only on initial levels inside it](levels-congr.md)
- [Parallel composition of comparator lists on adjacent blocks](append-disjoint.md)
- [Swapping the wires of every comparator does not change levels](levels-swap.md)

## Tabulated levels

- [Tabulated levels](levels-tab.md)
- [Tabulated levels agree with levels](get-d-levels-tab.md)

## The bitonic networks

- [The half-cleaner has depth at most $1$](depth-le-half-cleaner.md)
- [The bitonic merger has depth at most $k$](depth-le-bitonic-merge.md)
- [Depth of the bitonic sorter's comparator list](depth-le-bitonic-sort-n.md)

## Every sorting network on `n` wires has depth at least `log₂ n`

- [Influence sets of wires](influence.md)
- [Influence sets grow at most exponentially with the level](card-influence-le.md)
- [Outputs depend only on the influence set](run-n-congr-influence.md)
- [Comparators inside $(0, n)$ keep a false value inside $(0, n)$](exists-false-run-n.md)
- [Sorting comparator lists on $n$ wires have depth at least $\log_2 n$](le-two-pow-of-sorts.md)
- [The bitonic sorting comparator list on $2^k$ wires has depth at least $k$](le-of-depth-le-bitonic-sort-n.md)

## Depth of `Network`s

- [Comparator list of a network](to-pairs.md)
- [Depth bound for a comparator network](depth-le-2.md)
- [Every sorting network on $n$ wires has depth at least $\log_2 n$](le-two-pow-of-sorts-2.md)
- [Batcher's bitonic sorting network has depth at most $k(k+1)/2$](bitonic-sorter-depth-le.md)
- [Batcher's bitonic sorter on $2^k$ wires has depth at least $k$](le-of-bitonic-sorter-depth-le.md)
