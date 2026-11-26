# Aggregate cost of stack operation sequences

For every stack $S$ and every sequence of
$n$ stack operations (PUSH, POP and MULTIPOP), if running the sequence on $S$ succeeds, that is,
no POP meets an empty stack, then its cost is at most $|S| + 2n$, where $|S|$ is the number of
elements of $S$.
