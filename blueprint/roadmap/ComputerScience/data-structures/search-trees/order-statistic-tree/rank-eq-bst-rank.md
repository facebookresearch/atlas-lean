# Cached rank agrees with traversal rank

Let $T$ be an order-statistic tree over a
linearly ordered key type whose cached subtree sizes are correct at every node and which is
ordered. Then for every query $q$, the rank of $q$ computed by descending $T$ with cached
left-subtree sizes equals the number of entries strictly smaller than $q$ in the inorder
traversal of the binary tree obtained by erasing the caches of $T$.
