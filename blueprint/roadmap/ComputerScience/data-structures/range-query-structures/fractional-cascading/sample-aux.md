# Alternating selection with a flag

For a flag $b$ (true or false) and a list $\ell$, the
alternating selection of $\ell$ with initial flag $b$ is defined by recursion on $\ell$: the empty
list gives the empty list; for a list with head $a$ and tail $\ell'$, if $b$ is true it keeps $a$
and continues on $\ell'$ with flag false, and if $b$ is false it drops $a$ and continues on
$\ell'$ with flag true.
