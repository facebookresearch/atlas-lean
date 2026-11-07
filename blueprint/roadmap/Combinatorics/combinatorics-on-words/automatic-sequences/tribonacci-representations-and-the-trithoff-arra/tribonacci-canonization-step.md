# One step of Tribonacci canonization

Let $w$ be a word of natural-number digits, written
most significant digit first, and let $v = 0w$ be $w$ padded with a $0$ on the left, with
positions numbered from $0$. If leftmost carrying applies to $v$, the step returns its result
(Step 1). Otherwise let $p$ be the position of the leftmost digit $\ge 2$ of $v$ (the improper
boundary), or the length of $v$ if there is no such digit. If $v$ has no position $p + 3$, the
step is undefined. Otherwise, if $v_{p-1} = 0$, the step (Step 2a) sets $v_{p-1}$ to $1$,
decreases $v_p$ by $2$ and increases $v_{p+3}$ by $1$, as in $0abcd \mapsto 1(a-2)bc(d+1)$; if
$v_{p-1} \ne 0$, the step (Step 2b) sets $v_{p-2}$ to $1$ and $v_{p-1}$ to $0$, decreases $v_p$
by $2$ and increases $v_{p+2}$ and $v_{p+3}$ by $1$, as in
$01a0cd \mapsto 10(a-2)0(c+1)(d+1)$. All other digits of $v$ are unchanged.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Section 6.1.
