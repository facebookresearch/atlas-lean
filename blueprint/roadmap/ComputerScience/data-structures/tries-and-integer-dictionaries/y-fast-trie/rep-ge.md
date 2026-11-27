# Least representative at or above a key

For a grouped y-fast trie $t$ and a key $x$,
the result is $x$ itself if the membership test of the representative x-fast trie of $t$ (a
single probe of its deepest level) reports $x$ as present. Otherwise it is the successor of $x$
in the representative x-fast trie, that is, the least representative greater than $x$, or
nothing if there is none.

When $t$ is valid, the result is the least representative $r$ with $x \le r$, and nothing
when there is no such representative.
