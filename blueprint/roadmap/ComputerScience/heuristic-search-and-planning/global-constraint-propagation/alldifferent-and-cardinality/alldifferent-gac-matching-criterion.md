# Generalized arc consistency of ALLDIFFERENT by matchings

An ALLDIFFERENT constraint is generalized arc consistent exactly when every edge of its value graph lies in some matching that covers all the variables (Régin, 1994).

Let $C=\mathrm{ALLDIFFERENT}(x_1,\dots,x_p)$ with domains $D_1,\dots,D_p$ and [value graph](alldifferent-constraint.md) $GV(C)=(X_C,D(X_C),E)$.

**Theorem.** A value $a\in D_i$ has a support on $C$ iff the edge $(x_i,a)$ belongs to a matching of $GV(C)$ that covers $X_C$. Hence $C$ is [generalized arc consistent](../generalized-arc-consistency.md) iff every edge of $GV(C)$ belongs to a matching covering $X_C$, and the GAC closure of the domains keeps exactly the edges lying in some covering matching.

In particular, after one maximum matching $M$ is computed: if $|M|<p$ no value has a support and the propagator reports a wipe-out; if $|M|=p$, the values to delete are the edges lying in no maximum matching of $GV(C)$.

## Depends on

- [The ALLDIFFERENT constraint and its value graph](alldifferent-constraint.md): value graph and covering matchings.
- [Generalized arc consistency](../generalized-arc-consistency.md): supports and GAC.

## Proof depends on

None.

## Expansion

By the bijection between allowed tuples and covering matchings, a support of $x_i=a$ is an allowed tuple using $a$ for $x_i$, i.e. a covering matching containing $(x_i,a)$. If some covering matching exists then the covering matchings are exactly the maximum matchings (they have $p$ edges, the largest possible), which gives the last sentence.

Régin's proof of Theorem 1 is the same argument for a CSP whose constraints of difference are all required to be arc consistent ("diff-arc-consistent"). Representing $C$ by the binary constraints $x_u\ne x_v$ prunes strictly less: with $D_1=D_2=\{a,b\}$ and $D_3=\{a,b,c\}$ the binary decomposition is arc consistent, while GAC on $C$ removes $a$ and $b$ from $D_3$.

## Sources

- J.-C. Régin, "A filtering algorithm for constraints of difference in CSPs", *Proceedings of the Twelfth National Conference on Artificial Intelligence (AAAI-94)*, AAAI Press (1994), 362–367, [https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/](https://aaai.org/papers/00362-AAAI94-055-a-filtering-algorithm-for-constraints-of-difference-in-csps/). Theorem 1 and its proof, Algorithm 1, and the three-variable example of Figure 1, pp. 362–364.
