# Instrumented overlap search

Given a query interval $q = [c, d]$ and an interval tree
$T$, the instrumented overlap search returns an optional entry together with a cost record,
defined by recursion on $T$. On the empty tree it returns no entry and records one node visit.
At a node with left subtree $L$, entry $e$ with interval $[a, b]$ and right subtree $R$, it
first tests overlap by evaluating $a \le d$ and, only if that holds, $c \le b$; let
$k \in \{1, 2\}$ be the number of relations evaluated. If both hold, it returns $e$ and records
one node visit and $k$ endpoint comparisons. Otherwise, if $L$ is empty, it returns the result of
searching $R$, adding one node visit and $k$ endpoint comparisons to that search's cost. If $L$
is nonempty with cached maximum high endpoint $m$, it returns the result of searching $L$ when
$c \le m$ and of searching $R$ otherwise, adding one node visit, $k + 1$ endpoint comparisons and
one cached-maximum read to that search's cost. No other counter is ever incremented.
