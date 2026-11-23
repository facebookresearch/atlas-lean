# Irreducibility criterion

Let $L$ be the Leslie matrix of $m + 1$ age classes with nonnegative fertilities $f_0, \dots, f_m$, a
positive fertility $f_m$ of the last class, and positive survival coefficients $s_0, \dots, s_{m-1}$.
Then $L$ is irreducible: its entries are nonnegative, and for all age classes $i$ and $j$ (including
$i = j$) there is a sequence $i = i_0, i_1, \dots, i_k = j$ with $k \ge 1$ and $L_{i_{t-1} i_t} > 0$ for
$t = 1, \dots, k$. Indeed, one may descend from $i$ to $0$ one class at a time through the subdiagonal
entries $L_{a+1, a} = s_a > 0$, step from class $0$ to the last class $m$ through $L_{0, m} = f_m > 0$,
and descend from $m$ to $j$ in the same way; this takes $k = i + 1 + (m - j) \ge 1$ steps. Nothing is
assumed of $s_m$, which does not enter $L$.
