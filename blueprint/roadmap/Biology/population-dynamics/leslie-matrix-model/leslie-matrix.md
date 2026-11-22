# Leslie matrix

For real fertilities $f_0, \dots, f_{n-1}$ and real survival coefficients $s_0, \dots, s_{n-1}$ of $n$ age
classes, the Leslie matrix $L$ is the $n \times n$ real matrix with entries $L_{0, j} = f_j$,
$L_{j+1, j} = s_j$ and $0$ elsewhere; for $n = 0$ it is the empty matrix. For $n \ge 1$, its first row is
$(f_0, \dots, f_{n-1})$, its subdiagonal is $(s_0, \dots, s_{n-2})$, and the last coefficient $s_{n-1}$
does not enter $L$. In the demographic reading, $f_j \ge 0$ is the fertility of class $j$ and
$s_j \in [0, 1]$ the probability of surviving from class $j$ to class $j + 1$.
