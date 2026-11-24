# Ranked labeled history

For a natural number $n$, a ranked labeled history of $n$ labeled genes is a sequence of coalescence events indexed by the steps $i \in \{0, \dots, n-2\}$ (no step when $n \le 1$): at step $i$ there are $n - i$ lineages, labeled $0, \dots, n-i-1$, and the event is an [unordered pair of lineages](lineage-pair.md) among them, the pair that merges. The merged lineage takes the smaller label and the other lineages keep their relative order.
