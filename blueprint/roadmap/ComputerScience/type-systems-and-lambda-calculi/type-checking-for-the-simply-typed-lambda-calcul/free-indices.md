# Free indices of a raw term

For a binder depth $d$ and a raw term $t$, the free
indices of $t$ at depth $d$ form a list defined by recursion on $t$: a variable with index $n$
contributes $[n - d]$ if $d \le n$ and the empty list otherwise; an application contributes
the free indices of the function followed by those of the argument, both at depth $d$; and a
lambda abstraction contributes the free indices of its body at depth $d + 1$.
