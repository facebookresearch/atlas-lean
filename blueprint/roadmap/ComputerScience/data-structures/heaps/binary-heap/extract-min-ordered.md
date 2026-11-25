# Extraction from a binary min-heap leaves a heap-ordered array

Let $h$ be a binary
min-heap over a linearly ordered type. If extracting the minimum from $h$ succeeds and returns a
value $x$ together with a heap $r$, then the level-order array of $r$ is heap ordered: every
entry other than the root is at least its parent entry.
