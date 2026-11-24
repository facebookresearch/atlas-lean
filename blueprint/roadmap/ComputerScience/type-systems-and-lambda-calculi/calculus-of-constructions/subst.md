# Substitution for a de Bruijn variable

For $k \in \mathbb{N}$ and terms $u$ and $t$, the
term $t[k := u]$ is defined by recursion on $t$. For a variable, $\#i[k := u]$ is $\#i$ if
$i < k$, is $u$ with every free variable raised by $k$ if $i = k$, and is $\#(i - 1)$ if
$i > k$. A sort is unchanged, $(f\,a)[k := u] = f[k := u]\,a[k := u]$,
$(\lambda (x : A).\, b)[k := u] = \lambda (x : A[k := u]).\, b[k + 1 := u]$, and
$(\Pi (x : A).\, B)[k := u] = \Pi (x : A[k := u]).\, B[k + 1 := u]$.
