# Scan count of smaller elements

For a value $x$ and a catalog $L$, the scan count of $x$ in
$L$ is the number of elements of $L$ that are $< x$, computed by a direct scan: it is $0$ for
the empty catalog, and for a catalog with head $a$ and tail $L'$ it is the scan count of $x$ in
$L'$, plus $1$ if $a < x$.
