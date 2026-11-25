# The adversary's offline matching

Let $A$ be an online matcher, $h$ a list of earlier
neighbour lists and $ps$ a list of gadgets, pairs $(u, v)$ of left vertices. The list
$\mathrm{opt}(A, h, ps)$ of left vertices is empty when $ps$ is empty. Otherwise, for the first
gadget $(u, v)$, let $x = v$ if $A$, after the history $h$, proposes $v$ for an arrival with
neighbour list $[u, v]$, and $x = u$ otherwise; the list starts with $u, v$ in the first case and
with $v, u$ in the second, and continues with $\mathrm{opt}(A, h', ps')$, where $h'$ is $h$
extended by the neighbour lists $[u, v]$ and $[x]$ and $ps'$ is the list of remaining gadgets.
