# Final dimensions of a block

Let $q$ be a natural number,
$(d_0, m_0), \dots, (d_{k-1}, m_{k-1})$ a list of blocks and $C$ a list of chains of branch steps.
The final dimension list of block $i$ is defined when $C$ has an entry $s_1, \dots, s_r$ at index
$i$: start from $N_i$ copies of $d_i$, where $N_i$ is the basic multiplicity of block $i$ (the
empty list when $i \ge k$), and for $t = 1, \dots, r$ in order apply the split replacement of step
$s_t = (a_t, b_t, c_t)$, which replaces $c_t$ copies of $a_t + b_t$ by $c_t$ copies of $a_t$ and
$c_t q^{a_t}$ copies of $b_t$. It is undefined when $C$ has no entry at index $i$ or when one of
these split replacements is undefined.
