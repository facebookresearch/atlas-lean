# Safe heap configurations

A heap configuration, consisting of a heap command, a store and
a heap, is safe when every heap configuration reachable from it in zero or more heap steps
either has command $\mathtt{skip}$ or can take a further heap step.
