# Slot holds a key

A slot of a cuckoo hash table is either empty or holds a pair $(k, v)$ of a
key and a value. For a slot $s$ and a key $k'$, this test is true when $s$ holds a pair whose key
is $k'$, and false when $s$ is empty or holds a pair with a different key.
