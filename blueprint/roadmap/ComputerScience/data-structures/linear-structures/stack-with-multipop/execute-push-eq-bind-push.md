# Running a PUSH agrees with the standalone PUSH

For every stack $S$, every value $x$ and
every finite sequence $\sigma$ of stack operations, running PUSH $x$ followed by $\sigma$ on $S$
has the same result and cost as first performing the standalone PUSH of $x$ on $S$ and then
running $\sigma$ on the resulting stack, the two costs being added.
