# A β-redex with a value argument evaluates as its contractum

Let $N$ be a term of type $D$
in a context $C, \Xi$ and let $v$ be a value of type $C$ in $\Xi$. Writing $N[v]$ for $N$ with its
newest free variable replaced by $v$, for every term $w$ of type $D$ the application
$(\lambda x. N)\, v$ evaluates to $w$ under call-by-value big-step evaluation if and only if $N[v]$
evaluates to $w$.
