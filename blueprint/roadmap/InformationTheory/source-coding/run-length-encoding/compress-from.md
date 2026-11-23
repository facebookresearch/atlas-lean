# Run-length compression from a pending run

For a bit $c$, a natural number $r$ and a
finite bit list $w$, the compression $C(c, r, w)$ of $w$ from the pending run $(c, r)$ is the
list of natural numbers defined by recursion on $w$. If $w$ is empty, $C(c, r, w)$ is the
one-entry list $(r)$. If $w$ is a bit $b$ followed by a list $w'$, then $C(c, r, w)$ is $r$
followed by $C(\lnot c, 1, w')$ when $b \ne c$; it is $255$, then $0$, followed by
$C(c, 1, w')$ when $b = c$ and $r = 255$; otherwise it is $C(c, r + 1, w')$.

Here $c$ is the bit of the current run and $r$ is its length so far.
