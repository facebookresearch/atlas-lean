# Erasure removes the key from every level

If $S$ is a valid skip list, $k$ is a key and
$i$ is a natural number, then the level-$i$ list of key-value pairs (levels numbered from $0$) of
the skip list obtained by erasing $k$ from $S$ is the level-$i$ list of $S$ with every pair whose
key equals $k$ removed, the remaining pairs kept in their order.
