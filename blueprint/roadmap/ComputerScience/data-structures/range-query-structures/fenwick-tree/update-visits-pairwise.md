# Fenwick update visits are strictly increasing

For any natural array length $n$ and
one-indexed start $i$, each index in the update visit list is strictly smaller than every
later one, so no stored entry is visited twice. For $i=0$ or $i>n$ the list is empty.
