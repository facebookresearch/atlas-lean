# The integrality gap of the subtour LP for metric TSP is below 3/2

There is an absolute constant $\epsilon > 10^{-36}$ such that for every metric TSP instance the max-entropy rounding algorithm returns a Hamiltonian cycle $H$ with $\mathbb{E}[c(H)] \le (\tfrac32-\epsilon)\,\mathrm{OPT}_{\mathrm{LP}}$. Consequently

$$
\sup_{(V,c)\ \text{metric}}\ \frac{\mathrm{OPT}}{\mathrm{OPT}_{\mathrm{LP}}} \le \frac32-10^{-36},
$$

while instance families with ratio tending to $\tfrac43$ show that this integrality gap is at least $\tfrac43$.

## Proof sketch

Re-run the analysis of the approximation theorem with every comparison made against $c^{\top}x$ instead of $\mathrm{OPT}$: the tree costs $c^{\top}x$ in expectation and the payments are charged to $x$ alone. The one place the original analysis used $\mathrm{OPT}$, to handle edges whose cuts are rarely even, is replaced by an LP-based charging argument. Wolsey's bound gives the $\tfrac32$ baseline that the reduction improves.

## Depends on

- [Subtour elimination LP of a metric TSP instance](subtour-elimination-lp.md)
- [Max-entropy rounding algorithm for metric TSP](max-entropy-tsp-algorithm.md)
- [Integrality gaps of linear programming relaxations](../lp-based-approximation/integrality-gaps-of-linear-programming.md)

## Proof depends on

- [Karlin-Klein-Oveis Gharan: max-entropy rounding beats 3/2 for metric TSP](kko-three-halves-minus-epsilon.md)
- [Wolsey's bound: tree plus minimum T-join costs at most 3/2 of the subtour LP](wolsey-three-halves-subtour.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Bound on the Integrality Gap of the Subtour LP for TSP", FOCS (2022), arXiv:2105.10043.
