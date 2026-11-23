# Absent identities carry no heap entry

Let $q$ be an indexed min queue over a linear
order $W$ with identities in $\{0, \dots, n-1\}$ and let $v$ be an identity. The position
vector of $q$ records no slot for $v$ if and only if no entry of the heap array of $q$ has
identity $v$.
