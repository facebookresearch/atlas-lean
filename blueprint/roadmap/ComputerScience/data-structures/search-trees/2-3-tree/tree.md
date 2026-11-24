# Height-indexed 2-3 trees

For a type $\alpha$ of keys, the 2-3 trees over $\alpha$ indexed
by height are generated as follows. The leaf is a tree of height $0$ and stores no key. For a
natural number $h$, a key $a$ and trees $l$, $r$ of height $h$, the 2-node with separator $a$
and children $l$, $r$ is a tree of height $h + 1$. For a natural number $h$, keys $a$, $b$ and
trees $l$, $m$, $r$ of height $h$, the 3-node with separators $a$, $b$ and children $l$, $m$,
$r$ is a tree of height $h + 1$. Hence all leaves of a tree of height $h$ lie at depth $h$.
