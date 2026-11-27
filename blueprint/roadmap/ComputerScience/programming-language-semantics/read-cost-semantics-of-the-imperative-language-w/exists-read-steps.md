# Every big-step execution has a read count

For every statement $c$ and states $s$ and $t$: if $c$ takes $s$ to $t$ in the big-step semantics, then there is a natural number $n$ with $c : s \Downarrow^n t$ in the counted big-step semantics.
