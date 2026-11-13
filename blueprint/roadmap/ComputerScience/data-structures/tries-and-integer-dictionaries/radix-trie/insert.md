# Insertion into a radix trie

Inserting a value $v$ at a key $k$ (a list of symbols) into a
radix trie works as follows. If $k$ is empty, the root's value becomes $v$. Otherwise let $c$ be
the first symbol of $k$. If no child edge of the root has a label starting with $c$, a new edge
labelled $k$ leading to a leaf storing $v$ is added after the existing edges. Otherwise take the
first such edge, with label $\ell$ and subtree $s$, let $q$ be the longest common prefix of $k$
and $\ell$, and replace that edge in place. If $k = \ell = q$, the edge keeps label $\ell$ and
leads to $s$ with its root value set to $v$. If $k = q$ but $\ell$ is longer, the edge is
labelled $q$ and leads to a new node storing $v$ whose only edge is the rest of $\ell$ leading
to $s$. If $\ell = q$ but $k$ is longer, the edge keeps label $\ell$ and leads to $s$ with $v$
inserted at the rest of $k$. If both are longer than $q$, the edge is labelled $q$ and leads to
a new node with no value and two edges: the rest of $\ell$ leading to $s$, then the rest of $k$
leading to a leaf storing $v$.
