# Joining separated ordered trees preserves order

Let $<$ be a relation on the keys, and let
$L$ and $R$ be red-black trees that are ordered for $<$ such that $a < b$ for every key $a$ of $L$
and every key $b$ of $R$. Then the join of $L$ and $R$, obtained by putting $R$ in place of the
empty right subtree of the rightmost node of $L$ (or $R$ itself if $L$ is empty) and keeping all
colors, is ordered.
