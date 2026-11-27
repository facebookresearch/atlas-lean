# Irrevocable matroid prefix rules

On a finite matroid with a fixed finite ground set, an online choice is a jointly measurable deterministic function of its permitted seed, observed sample or training prefix, and actual arrival prefix including the current label and weight. It cannot use future arrivals, and implements an independent accepted set by irrevocable Boolean decisions. A label observed for training is not also selected by a subsequent rule that excludes observed labels. The offline comparator is the maximum of the weights of the independent sets, with the empty set allowed. Separate models prescribe either one sample per ground label, an observation mask and a hidden vector, or a uniformly permuted training prefix; none lets an online rule inspect hidden actual weights of unarrived labels.

## Sources

- [Pinned source definition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatroidProphet.lean#L18-L87)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/MatroidSecretary.lean#L102-L231)
