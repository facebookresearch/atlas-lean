# The worms `0⋯0` lie below the worm `1`

For every $k$, $\langle 1 \rangle\top \vdash \langle 0 \rangle\langle 0 \rangle^k\top$ in RC, that is
$0^k <_0 1$. In the ordinal assignment of worms, $0^k$ has value $k$ and $1$ has value $\omega$.

Proof: induction on $k$. From $\langle 1 \rangle\top \vdash \langle 0 \rangle W_k$ with
$W_k = \langle 0 \rangle^k\top$, axiom 5 gives
$\langle 1 \rangle\top \wedge \langle 0 \rangle W_k \vdash \langle 1 \rangle(\top \wedge \langle 0 \rangle W_k)$,
monotonicity lowers $\langle 1 \rangle$ to $\langle 0 \rangle$, and dropping $\top$ gives
$\langle 0 \rangle\langle 0 \rangle W_k$.

## Informally uses

- [The Reflection Calculus RC](derives.md)

## Background

- [The order `<₀` on worms](worm-lt.md)

## Sources

- L. D. Beklemishev, "Provability algebras: an overview and current progress", slides, Steklov Mathematical Institute, 16 April 2012 (ordinal values $o(0^k) = k$ of worms).
