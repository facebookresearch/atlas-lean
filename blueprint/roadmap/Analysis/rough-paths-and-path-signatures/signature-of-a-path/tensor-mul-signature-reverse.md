# Time-reversed signature is the inverse

Let the velocity of $X$ be interval integrable on every interval, and let
$\overleftarrow{X}_u = X_{a+b-u}$ be its time reversal on $[a, b]$. Then

$$S(X)_{a,b} \otimes S(\overleftarrow{X})_{a,b} = 1$$

in the algebra of tensor series. Together with [Chen's identity](signature-eq-tensor-mul.md),
this makes the signatures of paths a group under $\otimes$, with inverse given by reversal; it is
why a path followed by its own reversal has the same signature as a constant path.

The source proves it through the coordinate formula
$S(\overleftarrow{X})^{i_1 \cdots i_k}_{a,b} = (-1)^k S(X)^{i_k \cdots i_1}_{a,b}$ (its
equation (22), [the coordinate form](signature-reverse.md), which holds for continuous velocity).
The identity (21) needs only a locally integrable velocity: it follows from Chen's identity at $b$,
$S(X)_{a,b} \otimes S(X)_{b,a} = S(X)_{a,a} = 1$, using
[the signature of the reversed path](signature-reverse-eq.md).

## Sources

- I. Chevyrev and A. Kormilitzin, *A primer on the signature method in machine learning*,
  arXiv:1603.03788v2, Definition 1.24 and Theorem 1.25, equation (21).
