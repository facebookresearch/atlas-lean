# Successful insertion into an indexed min queue

Let $q$ be an indexed min queue over a
linear order $W$ with identities in $\{0, \dots, n-1\}$, let $v$ be an identity and let
$k \in W \cup \{\top\}$, and suppose that inserting $v$ with key $k$ into $q$ returns the
queue $q'$. Then the heap of $q'$ is the binary min-heap push of the entry $(k, v)$ onto the
heap of $q$; the position vector of $q'$ records a slot $i$ for $v$, with $i$ less than the
size of the heap array of $q'$, and that array holds $(k, v)$ at index $i$; and every identity
$w \neq v$ has a recorded slot in $q'$ if and only if it has one in $q$.
