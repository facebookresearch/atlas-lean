# Strong law for finite irreducible Markov chains, including periodic chains

Let $P$ be an irreducible stochastic matrix on a finite nonempty set $S$,
with stationary probability vector $\pi$. For the [Markov chain](../finite-markov-chains/is-finite-markov-chain.md)
from any initial probability law and every $f:S\to\mathbb R$, almost surely

$$\frac1n\sum_{k=0}^{n-1}\mathbf1_{\{X_k=y\}}\longrightarrow\pi(y)
 \quad(y\in S),\qquad
 \frac1n\sum_{k=0}^{n-1}f(X_k)\longrightarrow\sum_y\pi(y)f(y).$$

No aperiodicity assumption is needed. If
$T_y^+=\inf\{n\ge1:X_n=y\}$ for a chain started at $y$, then
$\mathbb E_yT_y^+<\infty$ and $\pi(y)=1/\mathbb E_yT_y^+$.
The positive-time return convention is essential here.

## Depends on

- [Finite-state Markov chain](../finite-markov-chains/is-finite-markov-chain.md)

## Proof depends on

- [Strong Markov property at finite stopping times](../markov-and-strong-markov-properties/strong-markov-chain-ae-finite.md)
- [Finite absorption and its geometric tail argument](../finite-markov-chains/absorption-probabilities-and-mean-absorption-tim.md)
- [First Borel--Cantelli lemma](../../foundations/borel-cantelli-lemmas/first-borel-cantelli-lemma/measure-limsup-at-top-eq-zero.md)

## Expansion

Irreducibility gives a positive-probability path to $y$ from every state;
finite-state minimization gives a uniform geometric block tail for the
first hit. Apply the same argument after one step from $y$ to the first
positive return. Thus hit and return times have finite second moments.
After the first hit, successive return increments are iid by strong
Markov, with mean $a=\mathbb E_yT_y^+\ge1$ and finite variance.
Their partial sums divided by the number of returns converge to $a$:
Chebyshev on square indices has summable failure probabilities, so
Borel--Cantelli gives convergence there; nonnegative increments and the
ratio of consecutive squares tending to one squeeze all intervening
indices. Inverting these return-time sums gives visit frequency $1/a$.
The initial waiting time changes no limiting frequency.

For the identification with $\pi$, let
$v(z)=\mathbb E_y\sum_{k=0}^{T_y^+-1}\mathbf1_{\{X_k=z\}}$.
Conditional expectation and telescoping over the stopped cycle give
$vP=v$, $v(y)=1$ and $\sum_zv(z)=a$, so $v/a$ is stationary.
A stationary law on a finite irreducible chain has full support, by
propagating positive mass along paths. If $\eta$ is another stationary
law, $\eta(z)/\pi(z)$ is harmonic for the reversed stochastic matrix
$R(z,x)=\pi(x)P(x,z)/\pi(z)$. This matrix is irreducible; the maximum
principle forces every harmonic function to be constant. Normalization
then gives $\eta=\pi$. Hence $\pi(y)=1/a$.
The assertion for $f$ follows by a finite linear combination of visit
indicators.

For $P=\begin{psmallmatrix}1-a&a\\b&1-b\end{psmallmatrix}$ with
$0<a,b\le1$, $\pi=(b,a)/(a+b)$. In the periodic case $a=b=1$ every
trajectory alternates and the time averages converge to $(1/2,1/2)$,
although the one-time distribution from a point mass oscillates.

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th edition (2019), <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>, Theorem 5.6.1 and Theorem 5.5.11. The finite-variance regenerative strong law, return convention and stationarity identification are written out above without relying on a primitive-chain convergence theorem.
