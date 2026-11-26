# Polynomial commitment unconditional hiding

Fix a public key in the support of setup, a batch of evaluation indices chosen before the commitment, and its [honest observation law](polynomial-commitment-observation.md). Write $V$ for the full view: the commitment and the ordered list of evaluation triples. Write $B=b(V)$ for the same list with just the indices and field values. In particular, $B$ retains the number of disclosed points.

Let $v$ be a possible view, $i$ any index not disclosed in $v$, and $Y=f(i)$. Unconditional fresh-value hiding requires, for every field value $y$,

$$
\Pr[V=v,Y=y]\Pr[B=b(v)] = \Pr[V=v]\Pr[B=b(v),Y=y].
$$

This identity of joint masses also makes sense when the view has probability zero. For a positive-probability view it reads $\Pr[Y=y\mid V=v]=\Pr[Y=y\mid B=b(v)]$: even an unbounded observer gains nothing **in addition to** the public indices and values. It does not say that the latter data give no information, or that all guesses must miss. The freshness restriction matters: a disclosed value is already known exactly.

## Source

A. Kate, G. M. Zaverucha and I. Goldberg, [*Polynomial Commitments*](https://cacr.uwaterloo.ca/techreports/2010/cacr2010-10.pdf), CACR 2010-10, §3.1, Definition 3.1, p. 6, unconditional hiding. The conditional comparison specifies what information is already public in this batch model.
