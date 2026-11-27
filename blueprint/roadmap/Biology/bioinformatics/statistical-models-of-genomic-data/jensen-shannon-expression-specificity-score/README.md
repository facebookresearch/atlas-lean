# Jensen–Shannon expression-specificity score

A gene's specificity to one sample group (a tissue or tumor type) can be scored by the Jensen–Shannon divergence between its normalized expression profile across groups and the ideal profile concentrated on that group. Against a one-hot ideal, the divergence is a closed-form decreasing function of the group's expression share, which fixes how the score ranks genes.

- [Jensen–Shannon specificity against a one-hot expression profile](jensen-shannon-specificity-against-a-one-hot-profile.md)
