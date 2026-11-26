# Vector addition systems

A *vector addition system* of dimension $k \ge 1$ is a pair $(v, A)$ of a start vector $v \in \mathbb{Z}^k$ and a finite addition set $A \subseteq \mathbb{Z}^k$. A finite sequence $w_1, \dots, w_m$ in $\mathbb{Z}^k$ is a *path* in $(v, A)$ if $w_1 = v$ and $w_{i+1} - w_i \in A$ for every $i < m$. A vector $w \in \mathbb{N}^k$ is *reachable* if some path ending in $w$ has only nonnegative vectors on it; $R(v, A)$ is the set of reachable vectors and $C(v, A) = \{ w \in \mathbb{N}^k \mid w \le v_1 \text{ for some } v_1 \in R(v, A) \}$ the *coverability set*. The *covering problem* asks, given $(v, A)$ and $v_1 \in \mathbb{N}^k$, whether $v_1 \in C(v, A)$, and the *boundedness problem* whether $R(v, A)$ is finite. The size of a vector is the sum of the lengths of the binary representations of its components, and the size of a finite set of vectors is the sum of their sizes. Vector addition systems and [Petri nets](place-transition-petri-nets.md) are mathematically equivalent models.

## Depends on

- [Place/transition Petri nets](place-transition-petri-nets.md)

## Sources

- C. Rackoff, "The covering and boundedness problems for vector addition systems", *Theoretical Computer Science* 6:223–231, 1978, Definition 2.1 and the definitions of size and of the covering and boundedness problems in Section 2.
- J. Esparza and M. Nielsen, "Decidability issues for Petri nets – a survey", BRICS Report Series RS-94-8, Aarhus University, 1994, <https://arxiv.org/abs/2411.01592>, Section 1 (vector addition systems of Karp and Miller and their relation to Petri nets).
