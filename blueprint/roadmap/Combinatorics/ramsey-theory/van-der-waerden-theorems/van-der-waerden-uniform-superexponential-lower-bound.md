# Uniform superexponential lower bound for van der Waerden numbers

Define $W(r,k)$ as the infimum over positive integers $N$ such that every coloring $c:\mathbb N\to\{0,\ldots,r-1\}$ has $a,d\in\mathbb N$, $d>0$, $a+(k-1)d<N$, and $c(a+jd)=c(a)$ for every $j<k$. On the positive color and length range where the defining set is nonempty it is the least such $N$. There is a natural $K$ such that for all natural $k\ge K$ and $r\ge2$, in the reals

$$
W(r,k)>k^{k\lfloor\log_2 r\rfloor/100000}.
$$

## Depends on

- Van der Waerden interval convention with positive step and least positive forcing size.

## Proof outline

Use the existing finiteness statements only once their index convention is reconciled. Separate the lower-bound coloring construction and the argument uniform in the number of colors; keep the binary log floor and strict inequality.

- Uniform superexponential constructions of colorings without a long monochromatic progression and the passage from construction sizes to the strict lower bound.

## Sources

- [Comparator statement: `OAI.QuantitativeVanDerWaerden.uniform_lower_bound`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/QuantitativeVanDerWaerden.lean#L25-L30)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/160.md)
