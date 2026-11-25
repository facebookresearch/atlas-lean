# Accessible mutational paths in the House-of-Cards landscape

Let $L\ge1$ be an integer. On $\{0,1\}^L$, assign iid atomless real fitness
values and condition on a designated genotype $s_F$ being the global
maximum. Its antipode is $s_I$. No condition that $s_I$ is the global
minimum is imposed. A shortest mutational path from $s_I$ to $s_F$ has
$L$ single-coordinate changes, one for each coordinate. Call it accessible
when fitness strictly increases at each step. There are $L!$ such paths,
and in this House-of-Cards model

$$\mathbb E[\text{number of accessible shortest paths}\mid
            s_F\text{ is the global maximum}]=1.$$

Indeed, the $L$ nonterminal fitness values along any one path have uniformly
random relative order even under this conditioning. Each path is accessible
with probability $1/L!$, and linearity of expectation suffices; different
paths need not be independent.

For an additive landscape $f(x)=a+\sum_i s_ix_i$ with every $s_i>0$, all
$L!$ shortest paths from $0^L$ to $1^L$ are accessible. More generally every
strictly increasing nearest-neighbor path on the finite cube visits no
vertex twice and has at most $2^L-1$ edges. A maximal such path ends at a
local peak, not necessarily the global maximum.

## Expansion

Neutral plateaus and longer paths require their own definitions. Conditioning
also on the initial genotype being the global minimum changes the random
model. The mean count one does not establish a lower bound bounded away
from zero for the probability of at least one accessible path.

Franke et al. report simulations and conjectures for asymptotic existence
probabilities in particular tunable-ruggedness regimes, not a universal
proved limit of one. Their Rough Mount Fuji discussion conjectures the
positive-slope behavior; the unconditioned-start House-of-Cards discussion
instead reports an increasing probability of no accessible path. Those
asymptotics are not asserted as theorems here.

## Sources

- J. Franke, A. Klözer, J. A. G. M. de Visser and J. Krug, "Evolutionary accessibility of mutational pathways", PLoS Computational Biology 7 (2011), e1002134, <https://doi.org/10.1371/journal.pcbi.1002134>, Results, equation (2) and the House-of-Cards and Rough Mount Fuji discussions. The finite termination argument is given above.
