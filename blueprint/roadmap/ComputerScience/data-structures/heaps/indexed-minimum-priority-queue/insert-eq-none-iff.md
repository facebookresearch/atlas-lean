# Insertion fails exactly on present identities

Let $q$ be an indexed min queue over a
linear order $W$ with identities in $\{0, \dots, n-1\}$, let $v$ be an identity and let
$k \in W \cup \{\top\}$. Inserting $v$ with key $k$ into $q$ returns no queue if and only if
the position vector of $q$ records a slot for $v$.
