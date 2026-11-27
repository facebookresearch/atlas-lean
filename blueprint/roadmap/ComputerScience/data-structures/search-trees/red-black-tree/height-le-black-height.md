# Height of a red-black tree is at most twice its black height

Let $t$ be a red-black tree in which no red node has a red child and every root-to-leaf path
contains the same number of black nodes, and let $b$ be its black height, counting the empty
leaf as one black node. Then the height $h$ of $t$ as a binary tree satisfies

$$h + 2 \le 2b + \varepsilon,$$

where $\varepsilon = 1$ if the root of $t$ is red and $\varepsilon = 0$ otherwise.
