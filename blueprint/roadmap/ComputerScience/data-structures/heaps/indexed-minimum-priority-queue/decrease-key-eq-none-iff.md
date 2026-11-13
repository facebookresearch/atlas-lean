# Decrease-key fails exactly on absent identities and non-decreases

Let $q$ be an
indexed min queue over a linear order $W$ with identities in $\{0, \dots, n-1\}$, let $v$ be
an identity and let $k \in W$. Decreasing the key of $v$ to $k$ in $q$ returns no queue if and
only if either the position vector of $q$ records no slot for $v$, or it records a slot $i$
for $v$ with $i$ less than the size of the heap array of $q$ and $k$ is not strictly less, in
$W \cup \{\top\}$, than the key of the heap entry at index $i$.
