# A second serve of the same key returns the first response

For a handler $f$, a key $k$ and a memo table $t_0$, serve $k$ once and then serve $k$ again
on the resulting table: the second serve returns the same response as the first. This is a
statement about sequential table lookups only; it describes no concurrent execution.
