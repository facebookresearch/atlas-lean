# Size-weighted within-deme coalescence-time invariance

Let $d\ge1$, $c_i>0$, $C=\sum_i c_i$, and let $Q$ be an irreducible
finite migration rate matrix with stationary row probability vector
$\pi_i=c_i/C$. This is the conservative-migration hypothesis; detailed
balance is not required. Two lineages migrate independently with
ordered-pair generator
$\mathcal Lf(i,j)=\sum_kq_{ik}f(k,j)+\sum_kq_{jk}f(i,k)$.
While in $(i,i)$ they coalesce at rate $1/c_i$ and enter an absorbing
state. Write $g(i,j)$ for their mean absorption time. Then all these
means are finite and

$$\sum_i\frac{c_i}{C}g(i,i)=C.$$

This samples a deme with weights $c_i/C$ and places both lineages there.
It is not the same averaging law as two independent stationary deme
draws conditioned on equality, whose weights are proportional to
$\pi_i^2$.
Deme-transitive symmetry of the whole rate/size model implies
$g(i,i)=C$ for every deme. In general only the weighted identity holds.
For three unit-size demes with $q_{12}=q_{21}=1$,
$q_{23}=q_{32}=2$ and other off-diagonal rates zero,
$(g(1,1),g(2,2),g(3,3))=(394,444,413)/139$, averaging to three.

## Depends on

- [Finite continuous-time transition semigroup](../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)

## Background

- [Symmetric-island first-step equations](first-step-equations.md)
- [Symmetric-island within-deme mean](within-time.md)

## Expansion

The pair process is a finite nonexplosive chain. Irreducibility of $Q$
provides, from every pair state, a finite positive-rate path to a diagonal
state and then absorption. Over a fixed positive time interval each such
path has positive probability. Taking the minimum over finitely many
starting states yields a uniform positive absorption probability, hence
a geometric survival tail and finite $g$.
First-step conditioning on the next exponential holding time gives
$(\mathcal Lg)(i,j)-\mathbf1_{i=j}g(i,i)/c_i=-1$.
These are the equations of this general ordered-pair process, not an
application of the island-specific three-state definition.

Since $\pi Q=0$, the **unkilled** generator $\mathcal L$ has stationary
law $\pi\otimes\pi$. Summing the equations with weights $\pi_i\pi_j$
cancels its term and gives $\sum_i\pi_i^2g(i,i)/c_i=1$.
Substitution of $\pi_i=c_i/C$ proves the result.
For the displayed counterexample the means on unordered states
$11,12,13,22,23,33$ are respectively
$(788,1043,1109,888,963,826)/278$, which directly solve all six equations.
For $c=(1,2,3)$ and $q_{ij}=c_j$ off the diagonal, the weighted mean is
six. Nonreversible cyclic migration on three equal demes also satisfies
the identity. The isolated one-deme case has mean $c_1=C$.
Removing irreducibility is not harmless: with multiple nonmigrating
demes, the within-deme mean is $c_i$ and between-deme means are infinite.

## Sources

- C. Strobeck, "Average number of nucleotide differences in a sample from a single subpopulation: a test for population subdivision", Genetics 117 (1987), 149–153, <https://doi.org/10.1093/genetics/117.1.149>. The identity is derived above and the example solved exactly.
