# Rooted binary tree with transition weights

Let $L$ be a set of leaf labels, $S$ a set of character states and $R$ a set of weights. A rooted binary tree with transition weights is defined inductively: it is either a leaf with a label $l \in L$, or an internal node carrying two weight functions $P, Q : S \times S \to R$ and two subtrees (the left and right children), where $P(s, a)$ is the transition weight from state $s$ at the node to state $a$ at the left child and $Q$ the same for the right child.
