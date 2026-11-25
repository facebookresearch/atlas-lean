# The entrance dichotomy and finite expected absorption of a Λ-coalescent

Let $\Lambda$ be a nonzero finite measure on $[0,1]$ with
$\Lambda(\{1\})=0$. Start the [Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)
from singletons. Write $N(t)$ for its number of blocks, $T_n$ for the
absorption time of its restriction to $[n]$, and
$T_\infty=\sup_n T_n$, allowing the value infinity.
Exactly one of the following occurs:

- almost surely $N(t)<\infty$ for every $t>0$, and $\mathbb E T_\infty<\infty$;
- almost surely $N(t)=\infty$ for every $t>0$, and $T_\infty=\infty$.

Thus coming down from infinity is equivalent to finite expected absorption
time under the stated no-atom-at-one hypothesis. It is not merely a claim
about the eventual merger of each fixed finite sample.

## Depends on

- [The Λ-coalescent on the natural numbers](lambda-coalescent-on-n-as-a-time-indexed-cadlag.md)

## Expansion

Here is the entrance argument and the second-moment step behind the
expectation assertion. The finite restrictions can be driven by independent
binary clocks of rate $\Lambda(\{0\})$ for each pair of block indices,
together with Poisson points of intensity $dt\,x^{-2}\Lambda(dx)$ for
$0<x<1$. At a point of size $x$, mark blocks independently with probability
$x$ and merge the marked blocks if there are at least two. Blocks are
indexed by their least elements. The rate visible to a restriction of size
$n$ is finite, since the probability of at least two marks is at most
$\binom n2x^2$. These consistent restrictions have the specified merger
rates and hence the prescribed path law. Independent driving increments
and right continuity give the strong Markov restart property; alternatively
one obtains it first for stopping times on dyadic grids and then by decreasing
approximation, on each finite cylinder.

Let $\tau=\inf\{t:N(t)<\infty\}$. The event $\{\tau=0\}$ belongs to the
germ of the independent driving increments at zero. It is independent of
every finite collection of time strips $(1/(j+1),1/j]$, hence of itself;
its probability is zero or one. Restart from any partition with infinitely
many blocks has the same block-count law as restart from singletons,
by enumerating its blocks by least elements and using the block-index merger
rates. If that zero-time entrance probability is zero but
$0<\tau<\infty$, then $N(\tau)$ must be finite: otherwise strong Markov
restart from an infinite partition would have entrance time zero, contrary
to that zero probability. This would be a jump from infinitely many blocks
to finitely many. A binary merger cannot do that, and a Poisson event with
$x<1$ leaves infinitely many blocks unmarked almost surely. There are only
countably many driving events, so no such jump occurs. Thus either
$\tau=0$ almost surely or $\tau=\infty$ almost surely. Monotonicity of $N$
upgrades the assertions at rational positive times to all positive times.

In the first case the remaining absorption time after any positive time is
almost surely finite, because there are finitely many blocks and each
nonabsorbing finite state has a positive finite exit rate. To upgrade this
to finite expectation, set $a=\lambda_{2,2}=\Lambda([0,1])>0$ and
$A_m=\{T_m>T_{m-1}\}$ for $m\ge2$. On $A_m$, the restriction to $[m]$
has exactly two blocks at $T_{m-1}$, so strong Markov restart gives

$$\mathbb E T_\infty=a^{-1}\sum_{m=2}^{\infty}\mathbb P(A_m).$$

For $s_n=\sum_{m=2}^n\mathbb P(A_m)$ and
$Y_n=\sum_{m=2}^n\mathbf1_{A_m}$, restart at $T_k$ and order the remaining
blocks by their least labels. A later event $A_m$ can occur only when $m$
is one of these least labels; if its block is the $i$th, its conditional
probability is $\mathbb P(A_i)$. Consequently

$$\sum_{m=k+1}^n\mathbb P(A_k\cap A_m)\le\mathbb P(A_k)s_n,
 \qquad \mathbb E Y_n^2\le2s_n^2+s_n.$$

If $s_n\to\infty$, Cauchy--Schwarz applied above the threshold
$\theta s_n$, $0<\theta<1$, gives
$\mathbb P(Y_n>\theta s_n)\ge(1-\theta)^2s_n^2/(2s_n^2+s_n)$.
First let $n$ grow, then let the count threshold grow, then let
$\theta\downarrow0$. Infinitely many $A_m$ occur with probability at
least $1/2$. On this event there must be infinitely many blocks already at
$T_2>0$: if there were only finitely many then only their finitely many least
labels could index later $A_m$. This contradicts coming down at every
positive time. Thus $s_\infty<\infty$ in the coming-down case.
The other case has $T_\infty=\infty$, completing the equivalence.

The restriction at one is essential. For $\Lambda=\delta_1$, every finite
restriction and the infinite partition merge into one block at a common
Exp$(1)$ time. Its expected absorption time is one, but at a fixed $t>0$
it still has infinitely many blocks with probability $e^{-t}$, so it does
not come down from infinity in the stated sense.

## Sources

- J. Pitman, *Coalescents with multiple collisions*, Technical Report 495, revised March 23, 1999, <https://statistics.berkeley.edu/sites/default/files/tech-reports/495.pdf>, Theorem 1, Corollary 3 and Proposition 23 (pp. 3--4, 21--22). The binary-clock supplement realizes an atom at zero.
- J. Schweinsberg, "A necessary and sufficient condition for the Λ-coalescent to come down from infinity", Electronic Communications in Probability 5 (2000), 1--11, <https://www.maths.tcd.ie/EMIS/journals/EJP-ECP/article/download/1013/1013-3391-1-PB.pdf>, Proposition 5 and equation (11), pp. 4--5. The second-moment bound is written out above; divergence of unconditional event probabilities alone is not used as a conditional Borel--Cantelli hypothesis.
