# Reweighting one leaf occurrence

Suppose a leaf of weight $v$ occurs at depth $d$ in a
Huffman weight tree $T$, and let $r$ be a real number. Then there are a multiset $R$ of reals and
a Huffman weight tree $T'$ such that the multiset of leaf weights of $T$ is $\{v\} + R$, that of
$T'$ is $\{r\} + R$, the total leaf weight of $T'$ is that of $T$ plus $r - v$, the weighted
external path length of $T'$ is that of $T$ plus $d(r - v)$, and $T'$ has the same height as
$T$.
