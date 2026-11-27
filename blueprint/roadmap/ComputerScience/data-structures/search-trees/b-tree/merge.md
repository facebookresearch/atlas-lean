# Merging two B-tree nodes around a separator

Given a key $s$ and trees $L$ and $R$, the
merge of $L$ and $R$ around $s$ is defined as follows. If $L$ and $R$ are leaves with key lists
$k_1$ and $k_2$, it is the leaf with keys $k_1$, then $s$, then $k_2$. If $L$ and $R$ are internal
nodes with key lists $k_1, k_2$ and child lists $c_1, c_2$, it is the internal node with keys
$k_1$, then $s$, then $k_2$, and children $c_1$ followed by $c_2$. In every other case it is $L$.

In deletion from a B-tree of minimum degree $t$, it is applied to two trees of the same height
that each hold $t - 1$ keys at the root, so the merged node holds $2t - 1$ keys.
