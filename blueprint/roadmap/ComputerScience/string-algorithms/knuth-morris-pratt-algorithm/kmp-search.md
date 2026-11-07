# Knuth–Morris–Pratt search

For lists $p$ (the pattern) and $t$ (the text) over a type
with a boolean equality, KMP search for $p$ in $t$ returns either a zero-based offset or no
offset, together with a cost: the number of symbol comparisons it makes. If $p$ is empty, it
returns the offset $0$ at cost $0$. Otherwise it first builds the prefix table of $p$, a list of
entries each pairing a symbol with a failure value. The transition of a table from a state $s$
on a symbol $x$ is defined as follows. If $s$ is less than the number of entries and $x$ equals the
symbol of entry $s$ (counting from $0$), the result is $s + 1$. Otherwise the result is $0$ when
$s = 0$, and when $s > 0$ it is the transition from the failure value of entry $s - 1$ on $x$.
Starting from the empty table, each symbol $x$ of $p$ in turn is appended as a new entry, with
failure value the transition of the current table on $x$ from the state equal to its number of
entries. The search then reads $t$ from the left, starting in state $0$ and moving to the
transition of the table on each symbol read. The first time the state equals $|p|$, after $j$
symbols have been read, it returns the offset $j - |p|$. If this never happens, it returns no
offset. The cost counts every equality test between two symbols, both while the table is built
and while $t$ is scanned. List operations, array access and arithmetic cost nothing.

When the boolean equality is lawful, the returned offset is the least offset at which $p$ occurs
in $t$, and no offset is returned exactly when $p$ does not occur in $t$.
