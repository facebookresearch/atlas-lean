# One pair witnesses nonadditivity of every normalized two-quasitrace

There exists a separable unital complex $C^*$-algebra $A$ admitting a normalized two-quasitrace and two positive contractions $a,b$ such that every normalized two-quasitrace $\tau$ on $A$ satisfies $\operatorname{Re}(\tau(a+b)-\tau(a)-\tau(b))\geq1/144$. The contractions are chosen before $\tau$, and positivity means $x^*x$ for some $x$. Here a one-quasitrace $\tau:A\to\mathbb C$ has real nonnegative values on $x^*x$, equal values on $x^*x$ and $xx^*$, obeys $\tau(h+ik)=\tau(h)+i\tau(k)$ for self-adjoint $h,k$, and is complex linear on each closed commutative (possibly nonunital) star subalgebra. A two-quasitrace extends as a one-quasitrace on $M_2(A)$ along the upper-left corner; normalization is $\tau(1)=1$.

## Depends on
The stated matrix-corner extension and exact restriction to closed commutative star subalgebras.

## Proof depends on
Construction of the algebra and an actual normalized two-quasitrace, plus an inequality forcing the same signed defect at one pair for all such quasitraces.

## Expansion
Separate nonemptiness of the quasitrace class from the universal defect estimate. Verify the numerical $1/144$, positivity and unit bounds of both witnesses, and that the comparison is a real-part lower bound, not merely a nonzero absolute gap.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KaplanskyQuasitrace.lean#L48-L50) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/294.md).
