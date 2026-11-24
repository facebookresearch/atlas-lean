# Chunks of a list have length at most the chunk size

Let $n > 0$ and let $L$ be a list.
Split $L$ from left to right into consecutive chunks of size $n$: elements go into the current
chunk until it holds $n$ elements, then a new chunk is started. Every chunk produced has at most
$n$ elements.
