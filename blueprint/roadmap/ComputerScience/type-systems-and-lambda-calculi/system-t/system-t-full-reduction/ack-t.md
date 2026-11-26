# Ackermann's function in System T

The term
$\lambda m.\,\mathsf{R}\,(\lambda n.\,\mathsf{succ}\,n)\,
(\lambda f.\,\lambda \_.\,\lambda n.\,\mathsf{R}\,(f\,\underline{1})\,
(\lambda r.\,\lambda \_.\,f\,r)\,n)\,m$ of type
$\mathsf{nat} \Rightarrow \mathsf{nat} \Rightarrow \mathsf{nat}$, where $\underline{1}$ is the
numeral of $1$. The outer recursor works at type $\mathsf{nat} \Rightarrow \mathsf{nat}$: from
the function $f$ for $m$ it builds the function for $m + 1$, sending $n$ to $f^{n+1}(1)$, as in
Girard-Lafont-Taylor §7.3.2.
