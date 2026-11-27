# A root of multiplicity $r$ survives substitution

If $Q(X, Y)$ has a [root of multiplicity](has-root-mult.md) at least $r$ at $(a, b)$ and
$P \in F[X]$ satisfies $P(a) = b$, then $(X - a)^r$ divides $Q(X, P(X))$.

The substitution $Y \mapsto P(X)$ is a ring homomorphism $F[X][Y] \to F[X]$ sending $X - a$ to
itself and $Y - b$ to $P(X) - P(a)$, a multiple of $X - a$. It therefore maps the ideal
$(X - a, Y - b)^r$ into $(X - a)^r$.

## Sources

- V. Guruswami, A. Rudra, M. Sudan, *Essential Coding Theory*, draft of August 26, 2025, Lemma 12.2.11 and Claim 12.2.14.
