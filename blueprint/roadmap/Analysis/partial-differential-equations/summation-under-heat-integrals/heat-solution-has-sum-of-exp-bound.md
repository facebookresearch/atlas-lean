# Summing under whole-line heat evolution

Let $I$ be a countable index set, $f_i:\mathbb R\to\mathbb R$ almost-everywhere
strongly measurable, and let $(A_i)$ be a summable real family. Suppose $c\ge0$
and $|f_i(y)|\le A_i e^{c|y|}$ for every $i,y$. For every real heat parameter $t$
and spatial point $x$,

$$
\sum_{i\in I}P_t f_i(x)=P_t\left(\sum_{i\in I}f_i\right)(x),
$$

with convergence of the series on the left. For $t\le0$ the convention is $P_t f=f$.
The bound implies $A_i\ge0$; it need not be assumed separately. The functions
$f_i$ may have either sign and need not be continuous. Gaussian exponential
integrability supplies the majorant at positive heat times.

## Sources

James Nolen, [*Partial Differential Equations and Diffusion Processes*](https://math.stanford.edu/~ryzhik/STANFORD/STANF227-10/notes227-09.pdf), §2.4, formula (4.42), for the Gaussian Duhamel representation. The weighted series estimates and mild uniqueness here follow by domination, iteration and the exponential series; they do not invoke the stronger classical-regularity conclusion of Theorem 2.4.1.
