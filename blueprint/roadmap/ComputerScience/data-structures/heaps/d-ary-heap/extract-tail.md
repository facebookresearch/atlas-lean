# Removing the root of a $d$-ary min-heap

Let $h$ be a $d$-ary min-heap whose storage
array $a$ is nonempty. Removing the root of $h$ gives the heap of arity $d$ whose storage array
is empty if $a$ has one entry. Otherwise the last entry of $a$ replaces the root, the last
position is dropped, and the new root is repeatedly swapped with its smallest $d$-ary child
while that child is smaller.
