# Minimum extraction

Given an initial candidate $c$ in a linearly ordered type and a list
$L$, minimum extraction returns a pair $(m, r)$ together with a cost. If $L$ is empty, it returns
$c$ with the empty list at cost $0$. If $L$ has head $x$ and tail $L'$, it compares $x$ with $c$
at cost one: if $x < c$, it extracts from $L'$ with candidate $x$, obtaining $(m, r)$, and returns
$m$ with the list $c$ followed by $r$; otherwise it extracts from $L'$ with candidate $c$,
obtaining $(m, r)$, and returns $m$ with the list $x$ followed by $r$. The total cost is one plus
the cost of the recursive extraction.
