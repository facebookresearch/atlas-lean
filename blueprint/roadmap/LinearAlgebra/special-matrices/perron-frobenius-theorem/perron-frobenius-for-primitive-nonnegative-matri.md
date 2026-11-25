# Perron–Frobenius theorem for primitive nonnegative matrices

Let $M$ be a real square matrix indexed by a nonempty finite set $S$.
Assume its entries are nonnegative and it is primitive: $M^k$ has every
entry strictly positive for some integer $k\ge1$. Then its spectral
radius $r$ is positive, and there are strictly positive real vectors
$u,v$ with

$$Mu=ru,\qquad v^{\mathsf T}M=rv^{\mathsf T},\qquad
\sum_i u_i=1,\qquad v^{\mathsf T}u=1.$$

The eigenvalue $r$ has algebraic multiplicity one in the characteristic
polynomial of the complexification $M_{\mathbb C}$. Every other complex
eigenvalue $\mu$ satisfies $|\mu|<r$, and

$$r^{-n}M^n\longrightarrow uv^{\mathsf T}\qquad(n\to\infty),$$

entrywise and hence in every matrix norm on this finite-dimensional
space. No stochasticity or diagonalizability is assumed.
For $M=[2]$, the normalized vectors are $u=v=1$, $r=2$, and the
normalized powers equal $1$. The empty index set is excluded:
there is then no vector whose entries sum to one.

## Depends on

- [Complexification of a real matrix](to-complex-matrix.md)

## Proof depends on

- [Perron–Frobenius theorem for nonzero irreducible nonnegative matrices](perron-frobenius-2.md)
- [Primitive stochastic matrix powers converge to their stationary distribution](../../../Probability/markov-chains/convergence-theorem-for-finite-markov-chains/tendsto-pow-apply.md)

## Expansion

**Positive eigenvectors and matching eigenvalues.** Each entry of $M^k$
is a sum of nonnegative products along length-$k$ paths. Its positivity
supplies a positive path between every pair of indices, so $M$ is
irreducible and nonzero. The same applies to $M^{\mathsf T}$.
Apply the irreducible theorem to both. If their positive eigenvalues are
$r$ and $s$, their positive eigenvectors have $v^{\mathsf T}u>0$, and
$r v^{\mathsf T}u=v^{\mathsf T}Mu=s v^{\mathsf T}u$, so $s=r$.
Rescale $u$ and then $v$ to obtain the two displayed normalizations.
The irreducible theorem bounds every complex eigenvalue in modulus by
$r$; since $r$ itself is an eigenvalue, it is the spectral radius.

**Power convergence by stochastic conjugation.** Let $D$ be the diagonal
matrix with diagonal $u$. It is invertible, and

$$P=r^{-1}D^{-1}MD,\qquad P_{ij}=\frac{M_{ij}u_j}{r u_i},
\qquad \pi_i=u_i v_i.$$

The eigenvector equations show that $P$ is nonnegative with row sums
one, $\pi_i>0$, $\sum_i\pi_i=1$, and $\pi^{\mathsf T}P=\pi^{\mathsf T}$.
Moreover $(P^k)_{ij}=(M^k)_{ij}u_j/(r^k u_i)>0$.
All hypotheses of the linked stochastic convergence theorem therefore
hold. It gives $(P^n)_{ij}\to\pi_j$. Conjugating back yields
$r^{-n}(M^n)_{ij}\to u_i\pi_j/u_j=u_i v_j$.
This uses a canonical convergence theorem with its full hypotheses,
rather than an unstated spectral-radius-to-power-limit step.

**Simplicity and strict dominance.** Write $\Pi=uv^{\mathsf T}$.
The real entrywise limit also acts on complex vectors.
If $M_{\mathbb C}z=rz$, then $r^{-n}M_{\mathbb C}^nz=z$ for all $n$,
so the limit gives $z=\Pi z$. Thus the complex $r$-eigenspace is exactly
$\mathbb C u$.
The decomposition
$\mathbb C^S=\mathbb C u\oplus W$, $W=\ker v^{\mathsf T}$, is invariant
under $M_{\mathbb C}$. Its restriction $B$ to $W$ has no eigenvalue $r$:
such an eigenvector would be a multiple of $u$ in $W$, hence zero.
The characteristic polynomial factors as
$(T-r)\det(TI_W-B)$, whose second factor is nonzero at $r$.
This proves algebraic, not merely geometric, simplicity, including when
$W$ is zero-dimensional.

Finally suppose $M_{\mathbb C}z=\mu z$ with $z\ne0$, $\mu\ne r$ and
$|\mu|=r$. Pairing with $v$ gives $v^{\mathsf T}z=0$, so the power limit
would give $(\mu/r)^n z\to\Pi z=0$. Its norm is constantly $\lVert z\rVert>0$,
a contradiction. Together with the already established modulus bound,
this proves strict dominance. This argument does not assume that the
restriction $B$ is diagonalizable.

## Sources

- E. Seneta, *Non-negative Matrices and Markov Chains*, 2nd ed., Springer (1981), Chapter 1. The proof above is derived from the linked irreducible Perron–Frobenius and primitive stochastic-convergence contracts.
