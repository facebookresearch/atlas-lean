# Dyadic zero padding makes cyclic convolution linear

Let $d$ be a natural number and let $x$ and $y$ be signals of length $2^d$, with [zero extensions](zero-extend.md) $x^{(2^{d+1})}$ and $y^{(2^{d+1})}$ to length $2^{d+1}$. Then for every natural number $t < 2^{d+1} - 1$,

$$\bigl(x^{(2^{d+1})} \circledast y^{(2^{d+1})}\bigr)(t \bmod 2^{d+1}) = (x * y)(t).$$

This is the [general padding bound](padded-cyclic-eq-linear.md) with $M = K = 2^d$ and $N = 2^{d+1} \ge 2^d + 2^d - 1$.
