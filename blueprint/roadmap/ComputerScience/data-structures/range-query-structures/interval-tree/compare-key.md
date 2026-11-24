# Lexicographic comparison of keys

For keys $(a, i)$ and $(b, j)$ in
$\mathbb{Z} \times \mathbb{N}$ (a low endpoint and an occurrence identifier), the comparison
returns less-than if $a < b$, or if $a = b$ and $i < j$; greater-than if $a > b$, or if $a = b$
and $i > j$; and equal if $a = b$ and $i = j$.
