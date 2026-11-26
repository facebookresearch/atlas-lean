# Bryant's apply operation

For a binary Boolean operation $\mathrm{op}$ and binary decision
diagrams $t_1, t_2$, the diagram $A_{\mathrm{op}}(t_1, t_2)$ is defined by recursion. If $t_1$
and $t_2$ are leaves with values $a$ and $b$, it is the leaf with value $\mathrm{op}(a, b)$.
Otherwise let $v$ be the smallest variable tested at the root of $t_1$ or of $t_2$ (a leaf tests
none), and for $i = 1, 2$ let $\ell_i$ and $h_i$ be the low and high children of $t_i$ if its
root tests $v$, and $\ell_i = h_i = t_i$ otherwise. The result is
$\mathrm{mk}(v, A_{\mathrm{op}}(\ell_1, \ell_2), A_{\mathrm{op}}(h_1, h_2))$, where
$\mathrm{mk}(v, \ell, h)$ is $\ell$ if $\ell = h$, and otherwise the node testing $v$ with low
child $\ell$ and high child $h$.
