# Exact-budget metric k-median recovery from distinct proxies

Fix a polynomial $P\in\mathbb N[X]$, positive reals $\varepsilon,L_0$ and a rational $0<\mu\le1/4$ with $\mu\le\varepsilon/12$. Use the rational-matrix and feasible-output conventions of the [below-two endpoint](randomized-metric-k-median-below-two.md), with disjoint clients and candidates, integral distances strictly positive off the diagonal, and every distance at most $P(N)$ for $N=|\mathrm{clients}|+|\mathrm{candidates}|$. The input also supplies a subset of exactly $k$ candidates as its anchor. A certificate consists of a subset $O$ of the candidates of size $k$ and positive total cost, a good subset $G\subseteq O$, and for each member of $G$ a proxy **in the anchor set**, with distinct proxies for distinct good centers. Assign each client to the nearest member of $O$, breaking ties by smallest point index. The sum of costs of good clusters using their proxies is at most their original cost plus $\mu\operatorname{cost}(O)$, and $|O\setminus G|\le L_0\log N$.

There is one finite-alphabet TM2 binary seed algorithm of the kind used in the below-two endpoint, chosen after the fixed parameters but before the input or certificate. For each eligible instance and real $0<\zeta<1$, form the query word $w=\operatorname{pair}(\mathrm{metric\ bits},\mathrm{anchor\ mask}\mathbin{+\!+}1^{b})$, where $b=\lceil\log(1/\zeta)/\log2\rceil$ and $\operatorname{pair}$ interleaves the first word with leading 1 bits, ends it with 0, then appends the second word. If the selected algorithm has seed polynomial $R$, take $r=R(|w|)$ fair bits $s$, and run it on $\operatorname{pair}(w,s)$ with the same candidate-mask decoder. The charged work is exactly $|w|+r+T(|\operatorname{pair}(w,0^r)|)$, where $T$ is the selected machine’s time polynomial. It is the certified polynomial bound plus input and seed lengths, not the actual time of a seed-dependent run. One $c>0$ and integer $d\ge0$ bound this work by $c(N+1)^d(1+\log(1/\zeta))^d$ on the eligible inputs.

Every seed gives a feasible set of at most $k$ centers, and for every certificate the probability of cost at most $(1+2/\mathrm e+\varepsilon)\operatorname{cost}(O)$ is at least $1-\zeta$. The certificate is not part of the query or machine input, and the output need not use exactly $k$ centers.

## Depends on

- [Native finite-alphabet TM2 machine step, input and output](../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/finite-alphabet-tm2-binary-abi.md)
- Capped integral metric input with exact-size anchor, deterministic nearest-center assignment, comparison certificate, unary precision and finite seed law.

## Expansion

Separate the deterministic companion program from the recovery proof. For each real $\eta>0$, choose one deterministic polynomial-time program on the internal encoding `InstanceProgram.encode`, with a Boolean list as its unframed output. For every valid rational metric instance $I$, the list is the full vertex membership mask of a nonempty set $S$ of facilities with $|S|\le k$, and $\operatorname{cost}_I(S)\le(1+2/\mathrm e+\eta)\operatorname{OPT}(I)$, where the optimum is over those same feasible subsets. This is the internal form of the [deterministic metric k-median approximation](deterministic-metric-k-median-approximation.md): composing the program with the input parser gives the public binary computation. The recovery proof uses the internal program, not just its cost guarantee, and still does not read the comparison certificate.

## Proof outline

Separate the recovery inequality for an arbitrary certificate from the algorithm that reads only the metric and anchor. Prove the budget and success assertions for the same output distribution, then bound the total bit cost.

## Sources

- [Comparator statement: `OAI.MetricKMedianRecovery.RefinedRecovery.refined_recovery`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianRefinedRecovery.lean#L153-L164)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/125.md)
- [Bounded input, precise certificates, nested encoding and work bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/KMedianRefinedRecovery.lean#L65-L146)
- [Internal program and parser composition](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/KMedian/Main.lean#L24-L52), [mask and cost guarantee](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/KMedian/Model.lean#L45-L57), and [use in proxy recovery](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Combinatorics/KMedianRecovery/Refined/Recovery.lean#L8-L22).
