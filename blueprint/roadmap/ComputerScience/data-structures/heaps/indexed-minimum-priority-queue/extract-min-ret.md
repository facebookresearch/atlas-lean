# Successful extraction from an indexed min queue

Let $q$ be an indexed min queue over a
linear order $W$ with identities in $\{0, \dots, n-1\}$, and suppose that extracting the
minimum of $q$ returns the heap entry $e = (k, u)$, with key $k \in W \cup \{\top\}$ and
identity $u$, together with the queue $q'$. Then binary min-heap extraction on the heap of $q$
returns $e$ together with the heap of $q'$; the position vector of $q'$ records no slot for
$u$; and every identity $w \neq u$ has a recorded slot in $q'$ if and only if it has one in
$q$.
