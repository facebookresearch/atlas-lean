# Weight at a given depth

For a real number $v$, a weight tree $T$ and a natural number
$d$, the relation "$T$ contains $v$ at depth $d$" is defined inductively: the leaf of weight $v$
contains $v$ at depth $0$, and if $L$ contains $v$ at depth $d$ or $R$ contains $v$ at depth $d$,
then the fork with left subtree $L$ and right subtree $R$ contains $v$ at depth $d + 1$. Thus it
holds exactly when some leaf of $T$ of weight $v$ lies at depth $d$, the root being at depth $0$.
