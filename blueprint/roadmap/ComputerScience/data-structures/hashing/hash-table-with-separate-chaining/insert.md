# Insertion into a hash table

Inserting a key $k$ with value $v$ into a hash table with $m$
buckets and hash function $h$ keeps the bucket count and every bucket other than bucket
$h(k) \bmod m$, and replaces the chain at bucket $h(k) \bmod m$ by that chain with $k$ bound to
$v$: any earlier binding of $k$ in that chain is removed and the binding of $k$ to $v$ is added.
