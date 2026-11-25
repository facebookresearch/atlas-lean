# Ordered insertion into a list

For an element $x$ of a linearly ordered type, the ordered
insertion of $x$ into the empty list is $[x]$. For a list with head $a$ and tail $\ell$, it is
$x$ followed by the whole list if $x < a$; it is $a$ followed by the ordered insertion of $x$
into $\ell$ if $a < x$; and it is the list unchanged if $a = x$.

On a strictly increasing list a key that is already present is therefore ignored. On an unsorted
list a later duplicate is not detected: inserting $2$ into $[3, 2]$ gives $[2, 3, 2]$.
