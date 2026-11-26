# Water filling computes the max-min fair allocation

In the [network model](network-model-and-feasible-rate-allocations.md), assume every source uses at least one link. The *water-filling* (progressive filling) algorithm starts with all rates $0$ and raises the rates of all sources not yet stopped together, at the same pace, until some links become saturated; it then stops every source using a saturated link, and continues with the others until all sources are stopped. It terminates after at most $L$ rounds, and its result is the unique [max-min fair](max-min-fair-rate-allocations.md) allocation. In particular a max-min fair allocation exists.

**Proof.** Each round saturates at least one new link, so there are at most $L$ rounds. When a source is stopped it uses a saturated link on which every other source was stopped at the same time or earlier, with a rate no larger, so that link is a bottleneck for it, and it stays one afterwards. When all sources are stopped, every source has a bottleneck.

## Depends on

- [Max-min fair rate allocations](max-min-fair-rate-allocations.md)

## Proof depends on

- [Max-min fairness is equivalent to every source having a bottleneck](max-min-fairness-is-equivalent-to-every-source-having-a-bottleneck.md)
- [Uniqueness of the max-min fair allocation](uniqueness-of-the-max-min-fair-allocation.md)

## Sources

- J.-Y. Le Boudec, *Rate adaptation, congestion control and fairness: a tutorial*, EPFL, version of 1 November 2021, <https://leboudec.github.io/leboudec/latex/cc/LEB3132.pdf>, Section 1.2.1, the paragraph "The water-filling algorithm" and Theorem 1.2.4 with its proof.
