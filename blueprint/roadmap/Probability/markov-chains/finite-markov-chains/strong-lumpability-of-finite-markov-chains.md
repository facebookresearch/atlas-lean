# Strong lumpability onto the image of a finite Markov chain

Let $S,S'$ be finite nonempty sets and let $\varphi:S\to S'$ be
**surjective**. Put $V(x,a)=\mathbf1_{\{\varphi(x)=a\}}$.
If $P$ is stochastic and $PV=VP'$ for a real matrix $P'$ on $S'$, then
$P'$ is stochastic and, for every initial law, $\varphi(X_n)$ is a
Markov chain with matrix $P'$. Its Markov property holds both for the
filtration of $X$ relative to which $X$ is Markov and for its own
natural filtration.

If $Q$ is a rate matrix on $S$ and $QV=VQ'$, then $Q'$ is a rate matrix,
and for every $t\ge0$,

$$e^{tQ}V=Ve^{tQ'}.$$

The image of the canonical finite-state continuous-time chain has the
law of a chain with generator $Q'$. Its Markov property holds relative
to the natural filtration of $X$ and therefore its own natural filtration.
Equivalently, for bounded $g:S'\to\mathbb R$ and $0\le s\le t$,

$$\mathbb E[g(\varphi(X_t))\mid\mathcal F_s^X]
 =(e^{(t-s)Q}Vg)(X_s)=(e^{(t-s)Q'}g)(\varphi(X_s)).$$

For an arbitrary nonsurjective map, apply the result to $\varphi(S)$.
One may extend the quotient chain outside that image only by separately
choosing stochastic rows or rate-matrix rows there; the intertwining
equation does not impose them.

## Depends on

- [Finite-state Markov chain](is-finite-markov-chain.md)
- [Finite continuous-time transition semigroup](../finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)

## Proof depends on

- [Finite-dimensional distributions of the continuous-time path](../finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/ctmc-input-measure-real-ctmc-path-fdd.md)

## Expansion

Choose $x$ in the fiber over $a$. Then
$P'(a,b)=\sum_{\varphi(y)=b}P(x,y)$, which is nonnegative with row sum
one. Likewise $Q'(a,b)=\sum_{\varphi(y)=b}Q(x,y)$; for $b\ne a$ every
summand is off-diagonal and nonnegative, and the row sum is zero.
Induction gives $P^nV=V(P')^n$ and $Q^nV=V(Q')^n$; absolute convergence
of finite matrix exponential series yields the semigroup identity.

In continuous time, the canonical path's full finite-dimensional
product formula gives the conditional expectation first when conditioning
on any finite collection of times up to $s$, by inserting $s$ into that
grid. A monotone-class argument over the past cylinders gives the formula
for $\mathcal F_s^X$. This uses the full finite-dimensional law, not only
a current-state/future joint identity. The discrete-time case uses the
assumed Markov property directly. The tower property passes each identity
to the smaller image filtration. Finite-state cadlag paths remain cadlag
after applying $\varphi$, so their image law is the claimed finite chain.

For the need to control unused rows, take $S=\{x\}$, $S'=\{a,b\}$,
$\varphi(x)=a$, $P=[1]$, $Q=[0]$. Both
$P'=\begin{psmallmatrix}1&0\\0&2\end{psmallmatrix}$ and
$Q'=\begin{psmallmatrix}0&0\\-1&1\end{psmallmatrix}$ satisfy the
respective intertwining equations, but neither is a valid quotient
transition/rate matrix on all of $S'$.

## Sources

- The finite matrix, conditional-expectation and unused-row arguments are derived above. The canonical path's finite-dimensional law is the precise continuous-time prerequisite.
