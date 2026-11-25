# The alternating-bit protocol is observation congruent to a one-place buffer

In the
labelled transition system of the protocol's recursive CCS specification, the data-free
alternating-bit protocol over lossy one-place channels is rooted weakly bisimilar (observation
congruent) to the one-place buffer
$\mathit{buf} = \mathit{acc}.\overline{\mathit{del}}.\mathit{buf}$.

This is stronger than weak bisimilarity; it holds because initially neither process can move
silently.
