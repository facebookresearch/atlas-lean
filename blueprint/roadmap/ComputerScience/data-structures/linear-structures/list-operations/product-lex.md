# Pairwise relations on list products in lexicographic order

Let $r_1$ be a relation on a type $A$ and $r_2$ a relation on a type $B$. Say that a list is
pairwise related by a relation $r$ if $r(x, y)$ holds whenever $x$ occurs at an earlier position
than $y$. Let $L$ be a list of elements of $A$ pairwise related by $r_1$ and $M$ a list of elements
of $B$ pairwise related by $r_2$. Then the list of all pairs $(a, b)$ with $a$ in $L$ and $b$ in
$M$, ordered first by the position of $a$ in $L$ and then by the position of $b$ in $M$, is
pairwise related by the lexicographic relation: $(a, b)$ is related to $(a', b')$ when
$r_1(a, a')$ holds, or $a = a'$ and $r_2(b, b')$ holds.
