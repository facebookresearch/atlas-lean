# Membership query of a grouped y-fast trie

Given a grouped y-fast trie $t$ over $w$-bit
keys and a key $x$, the query first finds a representative $r$: $r = x$ if the membership probe of
the representative x-fast trie accepts $x$, and otherwise $r$ is the successor of $x$ in the
representative trie. If there is no such $r$, the query returns false. Otherwise it returns
whether $x$ belongs to the group owned by $r$, namely the first group of $t$ whose last element is
$r$ (the empty list if there is none).
