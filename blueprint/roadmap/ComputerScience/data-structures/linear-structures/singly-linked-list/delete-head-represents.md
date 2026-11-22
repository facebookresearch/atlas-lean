# Deleting the head removes the first identity

Fix a capacity $n$, let $s$ be a store
assigning to each identity below $n$ either nothing or a singly linked list node, and suppose that
$s$ with head $h$ represents the list of identities $L$, where $h$ is an identity below $n$ or NIL.
Let $(s', h')$ be the store and head returned by deleting the head of $s$ with head $h$. Then $s'$
with head $h'$ represents $L$ with its first entry removed, which is the empty list when $L$ is
empty.
