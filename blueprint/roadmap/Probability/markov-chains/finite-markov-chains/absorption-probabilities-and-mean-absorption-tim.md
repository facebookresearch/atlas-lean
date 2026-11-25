# Absorption probabilities and mean times of a finite Markov chain

Let $P$ be a stochastic matrix on a finite nonempty state set $S$, and
let $X_n$ have its [Markov-chain law](is-finite-markov-chain.md).
Let $A\subseteq S$ be absorbing and assume that
$T=\inf\{n\ge0:X_n\in A\}$ is finite almost surely from every state.
For $B\subseteq A$, $h(x)=\mathbb P_x(X_T\in B)$ is the unique real
solution of

$$h=Ph\text{ on }S\setminus A,\qquad h=\mathbf1_B\text{ on }A.$$

The expectations $k(x)=\mathbb E_xT$ are finite and give the unique real
solution of

$$k=1+Pk\text{ on }S\setminus A,\qquad k=0\text{ on }A.$$

If $A=S$, these are simply $h=\mathbf1_B$ and $k=0$.

## Depends on

- [Finite-state Markov chain](is-finite-markov-chain.md)

## Proof depends on

- [Discrete Dynkin martingale](../markov-and-strong-markov-properties/dynkin-martingale-of-a-discrete-time-markov-chai.md)
- [Optional stopping at bounded stopping times](../../martingales/optional-stopping-theorem/expected-stopped-value-eq.md)

## Expansion

Almost-sure accessibility gives a positive-probability path from each
state to $A$. Remove loops to give a path of length at most $|S|$.
The minimum of the finitely many chosen path probabilities is
$\delta>0$. By conditioning at deterministic multiples of $|S|$,
$\mathbb P_x(T>n|S|)\le(1-\delta)^n$. Thus all mean hitting times are
finite. First-step conditioning proves both equations.
For uniqueness, the difference $g$ of two solutions satisfies $g=Pg$
off $A$ and is zero on $A$. Since $A$ is absorbing, it is harmonic there
as well. The Dynkin result and optional stopping imply
$g(x)=\mathbb E_x g(X_{n\wedge T})$. Bounded convergence and finiteness
of $S$ give $g(x)=0$. Without almost-sure absorption the uniqueness and
finite-mean assertions can fail, for instance when a nonabsorbing state
is itself fixed forever.

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th edition (2019), <https://services.math.duke.edu/~rtd/PTE/PTE5_011119.pdf>, Theorem 5.3.10 and its stopped-martingale proof pattern. The general finite-chain existence, geometric tail and uniqueness arguments are explicit above.
