# No deterministic online matcher beats ratio $1/2$, with any additive constant

Let
$(A_n)_{n \in \mathbb{N}}$ be a family of online matchers, $A_n$ having $2n$ left vertices, and
let $b$, $c$, $d$ be natural numbers with $d < 2c$. Then for some $n$ there are a sequence
$\sigma$ of arrivals on the left vertices of $A_n$ and a perfect matching $m$ of $\sigma$ such
that $d \cdot \mathrm{ALG} + b < c \cdot |m|$, where $\mathrm{ALG}$ is the number of arrivals of
$\sigma$ that $A_n$ matches when run from the empty history with no left vertex matched, and
$|m|$ is the length of $m$.

For $d > 0$ this says that the family is not $c/d$-competitive, whatever the additive constant.
