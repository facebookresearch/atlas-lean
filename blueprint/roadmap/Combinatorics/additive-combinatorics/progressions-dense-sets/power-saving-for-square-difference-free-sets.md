# Power saving for square-difference-free sets

There are real constants $c>0$ and $C$ such that for every integer $N\ge1$ and every $A\subseteq\{1,\ldots,N\}$,

$$
\bigl(\forall a,b\in A\;\forall m\in\mathbb N_{\ge1},\; a-b\ne m^2\bigr)\quad\Longrightarrow\quad |A|\le C N^{1-c}.
$$

Here subtraction is in the integers, both orders of a pair are tested, and zero is not a forbidden difference. The constants are independent of $N$ and $A$.

## Depends on

- Finite integer intervals, cardinality of their subsets, and real powers with a positive integer base.

## Expansion

Separate the signed square-kernel estimate on finite ordered intervals and the step-fiber transfer on each shorter square-progression interval, then the good-residue contraction with exceptional-prime and ceiling terms. These are usable for the signed functional without the final density lower bound. Sum the recurrence and use the density estimate only in proving the leaf's power saving.

## Proof outline

First state the ordered square-kernel estimate and the transfer of the signed functional along each square-step fiber. Next quantify the good-residue proportion and contraction, and bound the exceptional terms with the ceiling error in the shorter lengths. Finally prove power decay of the maximal functional and use its density lower bound to recover the cardinality estimate, including the finite initial range of $N$.

## Related results

This finite power bound implies the [Furstenberg–Sárközy theorem](furstenberg-s-rk-zy-theorem/furstenberg-sarkozy.md): translate a square-difference-free section of an infinite set from $[0,N)$ to $[1,N]$; its density is then at most $C N^{-c}$, which tends to zero. The qualitative theorem does not give the power bound.

## Sources

- [Comparator statement: `OAI.SquareDifference.power_saving`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SquareDifference.lean#L10-L15)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/182.md)
- [A power saving for square-difference-free sets, including the contraction, transfer and induction steps](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/A-power-saving-for-square-difference-free-sets-September-24-2026/paper.pdf)
- [Proof of the reduction and the prerequisite interfaces](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/SquareDifference/Main.lean)
