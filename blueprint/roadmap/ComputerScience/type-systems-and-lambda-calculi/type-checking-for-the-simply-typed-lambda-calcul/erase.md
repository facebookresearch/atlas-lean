# Erasure of intrinsically typed terms

The erasure of an intrinsically typed term in a
context $\Gamma$ is the raw term defined by recursion: a variable becomes the raw variable whose
index is its position in $\Gamma$ (counting from $0$ at the front); an application of $f$ to $a$
becomes the raw application of the erasure of $f$ to the erasure of $a$; and a lambda with
parameter type $B$ becomes the raw lambda annotated with $B$ whose body is the erasure of its
body. Erasure thus forgets all typing information except the binder annotations.
