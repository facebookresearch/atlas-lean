# Oblivious-sequence specification of a randomized data structure

An *oblivious-sequence specification* over an operation set $\mathsf{Op}$ with result sets $\mathsf{Res}(o)$ consists of a predicate $\mathsf{ValidSeq}$ on finite operation sequences and, for every valid sequence $\sigma = (o_1, \dots, o_m)$, a predicate $\mathsf{Contract}(\sigma, \mu)$ on probability distributions $\mu$ over transcripts $(a_1, \dots, a_m)$ with $a_i \in \mathsf{Res}(o_i)$.

The caller is *oblivious*: it fixes $\sigma$ before any randomness of the implementation is drawn. A state-transition specification $D$ with initial state $s_0$ induces the oblivious-sequence specification whose contract requires every transcript in the support of $\mu$ to be a valid transcript of $D$ from $s_0$ (zero error); bounded-error contracts, such as a false-positive probability bound per query, are also expressible.

## Depends on

- [State-transition specification of a data structure](state-transition-specification.md)

## Sources

- M. Mitzenmacher and E. Upfal, "Probability and Computing", 2nd edition, Cambridge University Press, 2017.
- A. Borodin and R. El-Yaniv, "Online Computation and Competitive Analysis", Cambridge University Press, 1998.
