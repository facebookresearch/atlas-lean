# Randomized metric k-median approximation below two

The input consists of labelled points covered by the union of its client and candidate sets, a nonempty candidate set, an integer budget $k>0$, and a symmetric nonnegative rational distance matrix with zero diagonal and the triangle inequality (distinct points may have distance zero). Feasibility means a subset of at most $k$ candidates, nonempty if there are clients. Its cost sums nearest-center distances over clients, or is zero if the selected set is empty. The comparison optimum is the minimum over **nonempty** candidate sets with at most $k$ elements.

Encode a natural by $\ell$ one bits then a zero then its $\ell$ low-to-high `Nat.bits`. A rational uses a bit indicating a negative numerator, then framed magnitude and denominator. The instance word $w$ gives the point count and budget, the full client and candidate membership masks, and the rational distance matrix in row-major order. For two words define $\operatorname{pair}(x,y)$ by writing $1b$ for each bit $b$ of $x$, then one zero bit, then $y$ unchanged. A binary randomized algorithm consists of a natural-coefficient polynomial $P$ and a deterministic [finite-alphabet TM2](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md) computation on pairs encoded by $\operatorname{pair}$, with unframed binary output. On input $w$, the seed $s$ is uniform over exactly $P(|w|)$ bits, and the machine is run on $\operatorname{pair}(w,s)$. Decode its result by retaining candidate indices with true bits at their positions; an absent bit is false.

There is an absolute $\sigma>0$ such that for each real $a>0$ one such algorithm returns a feasible decoded output for every instance and seed, has probability at least $1-(|\mathrm{clients}|+|\mathrm{candidates}|+2)^{-a}$ of cost at most $(2-\sigma)\mathrm{OPT}$ on every instance, and has expected cost at most $(2-\sigma)\mathrm{OPT}$ on every instance. Both statistics are averages over the full same seed space, including unsuccessful seeds.

## Depends on

- [Finite-alphabet TM2 and polynomial input/output computation](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Binary rational finite pseudometric input, nearest-center costs, and polynomial seed and multitape time model.

## Proof outline

Give the algorithm and the cost analysis over its entire seed law, not merely the successful component. Establish the binary execution bounds and compare the encoding with the deterministic k-median endpoint, which uses a strict metric and a different feasibility condition.

- Uniform below-two approximation, confidence amplification preserving all-seed feasibility, and a distinct expectation guarantee.

## Sources

- [Comparator statement: `OAI.MetricKMedianRecovery.global_application`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianRecovery.lean#L102-L104)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/125.md)
- [Pseudometric, feasible sets and exact encoders](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianRecovery.lean#L7-L58)
- [Paired input, seed length, decoded output and performance](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianRecovery.lean#L62-L100)
