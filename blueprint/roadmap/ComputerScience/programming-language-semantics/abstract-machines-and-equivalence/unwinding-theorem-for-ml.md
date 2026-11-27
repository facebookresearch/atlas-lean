# The unwinding theorem for recursive functions in ML

In [the ML fragment](an-ml-fragment-with-integer-references.md), let $f : ty \to ty', x : ty \vdash e : ty'$ and define the finite unwindings
$f_0 = \mathrm{fun}\ f = (x : ty) \to f\, x$ (which diverges when applied) and $f_{n+1} = \mathrm{fun}(x : ty) \to e[f_n/f]$. Then for every $f : ty \to ty' \vdash e' : ty''$ and every state $s$ whose domain contains the locations of $e$ and of $e'$,

$$s, e'[(\mathrm{fun}\ f = (x : ty) \to e)/f] \Downarrow \iff \exists n \ge 0.\ s, e'[f_n/f] \Downarrow.$$

The condition on $s$ matters: with $e = {!\ell}$, $e' = f$ and the empty state, the recursive function contains $\ell$ and cannot be evaluated, while $f_0$
contains no location and is already a value. Hence the recursive function is the least upper bound of its unwindings in the [contextual preorder](contextual-preorder-for-ml-with-references.md). The proof is by induction on
the structural characterization of frame-stack termination.

## Depends on

- [Contextual preorder for ML with references](contextual-preorder-for-ml-with-references.md)

## Proof depends on

- [Frame-stack termination for ML](frame-stack-termination-for-ml.md)

## Sources

- A. M. Pitts, "Operational semantics and program equivalence", in G. Barthe, P. Dybjer, L. Pinto and J. Saraiva (eds.), *Applied Semantics*, LNCS 2395, Springer, 2002, 378–412, <https://doi.org/10.1007/3-540-45699-6_8>: Section 5, equations (9) and (10) and Theorem 5.3 (an unwinding theorem) with its proof.
