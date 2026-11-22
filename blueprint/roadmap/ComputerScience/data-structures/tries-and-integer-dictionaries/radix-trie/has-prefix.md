# Prefix search in a radix trie

For a radix trie $t$ and a pattern $p$ (a list of symbols),
prefix search returns a boolean computed as follows. If $p$ is empty, it is true exactly when
$t$ stores at least one key. Otherwise let $c$ be the first symbol of $p$ and take the first
child edge of the root whose label starts with $c$; if there is none, the answer is false. If
that edge has label $\ell$ and subtree $s$, then: when $p$ is a prefix of $\ell$, the answer is
whether $s$ stores at least one key; otherwise, when $\ell$ is a prefix of $p$, the search
continues in $s$ with $p$ minus its first $|\ell|$ symbols; otherwise the answer is false.

On valid radix tries this decides whether some stored key has $p$ as a prefix.
