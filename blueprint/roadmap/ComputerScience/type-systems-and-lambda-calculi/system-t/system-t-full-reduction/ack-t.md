# Ackermann's function in System T

The term
$\lambda m.\,\mathsf{R}\,(\lambda n.\,\mathsf{succ}\,n)\,
(\lambda f.\,\lambda \_.\,\lambda n.\,\mathsf{R}\,(f\,\underline{1})\,
(\lambda r.\,\lambda \_.\,f\,r)\,n)\,m$ of type
$\mathsf{nat} \Rightarrow \mathsf{nat} \Rightarrow \mathsf{nat}$, where $\underline{1}$ is the
numeral of $1$. The outer recursor works at type $\mathsf{nat} \Rightarrow \mathsf{nat}$: from
the function $f$ for $m$ it builds the function for $m + 1$, sending $n$ to $f^{n+1}(1)$. This
adapts the iteration at higher type of Girard-Lafont-Taylor §7.3.2, whose iterator
$\mathrm{it}(f)$ sends $n$ to $f^n(1)$, with $\mathrm{it}(f)(0) = 1$: here the inner recursion
starts at $f(1)$, so the function for $m + 1$ sends $0$ to $f(1)$, matching
$\mathrm{ack}(m + 1, 0) = \mathrm{ack}(m, 1)$ for Mathlib's `ack`.
