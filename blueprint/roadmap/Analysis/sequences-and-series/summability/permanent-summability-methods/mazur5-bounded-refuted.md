# A permanent matrix for bounded asymptotically convergent sequences

The [bounded matrix summability claim](scottish-book-problem5-claim.md) holds with the definitions
used here. There is a real matrix that sums every ordinarily convergent real sequence to its
limit. For every bounded real sequence $x$ and $S\in\mathbb R$, it sums $x$ to $S$ exactly when
$x$ converges to $S$ along an increasing sequence of indices of density one.

## Proof

For each $n\ge1$, put $U_n=\{0,\ldots,n-1\}$. The $n$th block of the matrix has one row for each
$A\subseteq U_n$ with $2|A|\ge n$. The row assigns weight $1/|A|$ to the indices in $A$ and zero
to the other indices. Concatenate the finite nonempty blocks in increasing order of $n$. The row
series are finite sums. Convergence of the row sums to $S$ is equivalent to uniform convergence
to $S$ of all the admissible averages in the $n$th block as $n\to\infty$.

Write $y_k=x_k-S$. If $|y_k|\le M$ and $E_\eta=\{k:|y_k|\ge\eta\}$, the absolute value of the
average of $y$ over any admissible $A$ is at most $\eta+2M|E_\eta\cap U_n|/n$. Hence statistical
convergence to $S$ implies matrix summability to $S$ for bounded sequences. Ordinary convergence
implies both boundedness and statistical convergence, so the matrix is permanent.

Conversely, fix $\varepsilon>0$ and $0<\delta<\varepsilon$. If the rows sum $x$ to $S$, then in every
sufficiently late block all admissible averages of $y$ have absolute value less than $\delta$.
The set $P=\{k\in U_n:y_k\ge\varepsilon\}$ cannot be admissible, since its average would be at least
$\varepsilon$. Therefore $C=U_n\setminus P$ is admissible. Subtracting the contribution of $C$ from
the average over $U_n$ gives

$$
\varepsilon\frac{|P|}{n}\le \frac{1}{n}\sum_{k\in P}y_k\le 2\delta.
$$

Letting $\delta$ decrease to zero and repeating the argument with $-y$ gives statistical
convergence. Its equivalence with convergence on a density-one subsequence can be seen by using
cutoffs $N_j$ after which the exceptional set at tolerance $1/(j+1)$ has relative size at most
$1/(j+1)$. In each interval $[N_j,N_{j+1})$, retain the indices not exceptional at that tolerance.
If $n$ belongs to the $j$th interval, all discarded indices below $n$ lie in the exceptional set at
that interval's tolerance, so the retained set has density one. For its increasing enumeration
$s$, there are exactly $j$ retained indices below $s(j)$, hence $s(j)/j\to1$. Conversely, this ratio
implies counting density one: if $c(n)$ counts retained indices below $n$, then $n\le s(c(n))$, so
$c(n)/n$ is bounded between $c(n)/s(c(n))$ and $1$ for large $n$. Along the retained subsequence,
convergence leaves only finitely many exceptional indices at each fixed tolerance.

The same construction explains why one cannot choose a **single** density-one subsequence on
which all bounded sequences summed by this matrix converge. For any increasing candidate $s$,
the indicator of $\{s(m^2):m\in\mathbb N\}$ is statistically convergent to zero, but on $s$ it is
the indicator of the squares and does not converge.

## Sources

- S. Mazur, Problem 5 of the Scottish Book, addendum Ad 5(2), typescript p. 5 (printed p. 2),
  for the historical question and the assertion about a single subsequence. The block-matrix
  construction above concerns the matrix summability and asymptotic convergence definitions used
  here; it is not attributed to the typescript.
- [Counterexample to the negative assertion under these definitions](https://github.com/facebookresearch/atlas-lean/issues/8392),
  for the block-matrix construction and its proof.
