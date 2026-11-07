# Recorded positions lie inside the heap

Let $W$ be a linearly ordered type and let $q$
be an indexed min-queue over $W$ with identities in $\{0, \dots, n-1\}$. If the position
table of $q$ records slot $i$ for an identity $v$, then $i$ is less than the number of
entries currently stored in the heap array of $q$.
