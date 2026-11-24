# Erasing an address that the right heap of a union lacks

For heaps $h_1$ and $h_2$, let
$h_1 \cup h_2$ be their left-biased union (at an address allocated in both it keeps the value from
$h_1$). If the address $a$ is not allocated in $h_2$, then erasing $a$ from $h_1 \cup h_2$ gives
the union of $h_2$ with the heap obtained from $h_1$ by erasing $a$, taken with that heap on the
left.
