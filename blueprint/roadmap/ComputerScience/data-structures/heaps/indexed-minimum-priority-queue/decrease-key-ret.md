# Successful decrease-key

Let $q$ be an indexed min queue over a linear order $W$ with
identities in $\{0, \dots, n-1\}$, let $v$ be an identity and let $k \in W$, and suppose that
decreasing the key of $v$ to $k$ in $q$ returns the queue $q'$. Let $a$ be the heap array of
$q$. Then the position vector of $q$ records a slot $i$ for $v$ with $i$ less than the size of
$a$, $k$ is strictly less, in $W \cup \{\top\}$, than the key of the entry $a_i$, and the heap
array of $q'$ is obtained by sifting up from index $i$ the array that agrees with $a$ except
that $a_i$ is replaced by $(k, v)$. Moreover, every identity has a recorded slot in $q'$ if and
only if it has one in $q$.
