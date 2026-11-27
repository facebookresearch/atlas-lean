# A two-lineage isolation-with-migration law across a population split

Use backward time from sampling. For $0\le t<\tau$, where $\tau\ge0$
is finite, the two descendant populations have relative sizes
$c_1,c_2>0$ and finite backward migration rates $m_{12},m_{21}\ge0$.
At $\tau$ both populations merge into one ancestral population with
$c_A>0$. Before $\tau$, the pair chain has transient states $11,12,22$,
with rates $11\to12:2m_{12}$, $22\to12:2m_{21}$,
$12\to11:m_{21}$, $12\to22:m_{12}$, and coalescence rates
$1/c_1$ from $11$ and $1/c_2$ from $22$.
All other off-diagonal rates are zero; each full generator diagonal is
the negative total outgoing rate. Coalescence is absorbing.

If not absorbed by $\tau$, the remaining waiting time is a fresh
exponential variable of rate $1/c_A$, independent of the preceding
history. Let $A$ be the $3\times3$ transient subgenerator, including
coalescence in its diagonal, and $e_z$ the initial state row vector.
The survival law is

$$\mathbb P_z(T>t)=
\begin{cases}
e_ze^{tA}\mathbf1,&0\le t<\tau,\\
e_ze^{\tau A}\mathbf1\,e^{-(t-\tau)/c_A},&t\ge\tau.
\end{cases}$$

Consequently $\mathbb E_zT=\int_0^\tau e_ze^{tA}\mathbf1\,dt
+c_Ae_ze^{\tau A}\mathbf1\le\tau+c_A$.
Under pure isolation and sampling one gene from each population,

$$T\ \stackrel{d}=\ \tau+\operatorname{Exp}(1/c_A),
\qquad\mathbb E T=\tau+c_A,
\qquad\mathbb E D=\theta(\tau+c_A),$$

where the last identity requires the stated
[Poisson mutation-marking assumptions](expected-pairwise-differences-equal-theta-times.md).
For two genes initially in the same isolated population $i$, instead
$\mathbb E T=c_i(1-e^{-\tau/c_i})+c_Ae^{-\tau/c_i}$.
At $\tau=0$ all initial pair states have the ancestral exponential law.

## Depends on

- [Pairwise mutation-count identity](expected-pairwise-differences-equal-theta-times.md)

## Proof depends on

- [Finite continuous-time transition semigroup](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)

## Expansion

The factor two in same-deme migration counts either lineage; in the
mixed state only the lineage in the source population can move.
The finite semigroup gives survival mass before the split. Conditional
on survival to the split, the fresh ancestral exponential gives its tail
afterward. Integrating these two survival pieces proves the mean formula
without requiring $A$ to be invertible, important at zero migration.
Pure isolation from different populations precludes pre-split coalescence;
from the same population survival to $\tau$ has probability
$e^{-\tau/c_i}$, giving the two distinct formulas.

The algebraic specialization $c_A=(1+f)/2>0$ gives
$\mathbb E D=\theta(\tau+(1+f)/2)$ for the between-population isolation
case. Identifying $f$ with a particular published HKA demographic
parameter requires a source/model comparison; this substitution alone
is not that identification. No elementary diagonalized expression is
needed for the migration case, whose law is specified by the matrix
formula above. A general n-lineage history or likelihood is outside
this two-lineage result.

## Sources

- R. R. Hudson, M. Kreitman and M. Aguadé, "A test of neutral molecular evolution based on nucleotide data", Genetics 116 (1987), 153–159, <https://doi.org/10.1093/genetics/116.1.153> (divergence model). The chain and its pure-isolation law are derived above.
