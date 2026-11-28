# Big-step semantics of IMP counting while-body entries

The counted big-step relation $(c, s) \Downarrow_n s'$ relates a command $c$, an initial state $s$, a final state $s'$ and a count $n \in \mathbb{N}$; it is the least relation closed under the rules below, where $s[x \mapsto v]$ is $s$ with variable $x$ set to $v$.

- $(\mathtt{skip}, s) \Downarrow_0 s$ and $(x := a, s) \Downarrow_0 s[x \mapsto a(s)]$, where $a(s)$ is the value of $a$ in $s$.
- If $(c_1, s) \Downarrow_{n_1} m$ and $(c_2, m) \Downarrow_{n_2} f$, then $(c_1 ; c_2, s) \Downarrow_{n_1 + n_2} f$.
- If $g$ is true at $s$ and $(c_1, s) \Downarrow_n f$, then $(\mathtt{if}\ g\ \mathtt{then}\ c_1\ \mathtt{else}\ c_2, s) \Downarrow_n f$; if $g$ is false at $s$ and $(c_2, s) \Downarrow_n f$, the same conclusion holds.
- If $g$ is false at $s$, then $(\mathtt{while}\ g\ \mathtt{do}\ b, s) \Downarrow_0 s$.
- If $g$ is true at $s$, $(b, s) \Downarrow_{n_1} m$ and $(\mathtt{while}\ g\ \mathtt{do}\ b, m) \Downarrow_{n_2} f$, then $(\mathtt{while}\ g\ \mathtt{do}\ b, s) \Downarrow_{1 + n_1 + n_2} f$.

The count is the total number of entries into while-loop bodies; assignments, tests and skips cost nothing.
