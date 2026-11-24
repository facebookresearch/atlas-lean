# Finite-size lower bound for deterministic online matching

Let $n$, $b$, $c$, $d$ be
natural numbers with $d < 2c$ and $b < n$. For every online matcher $A$ with $2n$ left vertices
there are a sequence $\sigma$ of arrivals and a perfect matching $m$ of $\sigma$ such that
$d \cdot \mathrm{ALG} + b < c \cdot |m|$, where $\mathrm{ALG}$ is the number of arrivals of
$\sigma$ that $A$ matches when run from the empty history with no left vertex matched, and $|m|$
is the length of $m$.

At a fixed size some additive constant always suffices, which is why $b$ is bounded by $n$;
letting the size grow removes the bound.
