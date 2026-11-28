# MDP optimal-value decision is P-hard

Consider explicitly given finite MDPs with rational transition probabilities and rewards, encoded in
binary.

1. **Discounted case.** For a rational discount factor $0 < \gamma < 1$, deciding whether the optimal value $V^*(s)$
   from a given state is at least a given rational threshold is P-complete under logspace reductions: in P by
   linear programming, and P-hard by the reduction below.
2. **Finite horizon.** With the horizon $H$ given in unary, deciding whether the optimal $H$-step value is at least
   a threshold is P-complete: in P by backward induction, and P-hard by the same reduction. With $H$ in binary
   the backward-induction bound is not polynomial in the input size, and no claim is made for that encoding.

**Reduction.** The circuit value problem is P-complete under log-space many-one reductions, and replacing each
gate $g$ by a pair of gates computing $g$ and $\neg g$ (by De Morgan's laws, with negations moved to the inputs)
turns a circuit into an equivalent monotone circuit with AND and OR gates in logarithmic space. Given such a
circuit with $N$ gates and output gate $g_0$, let $H = N + 1$ and take states $(g, t)$ for gates $g$ and
$0 \le t \le H$. At an OR gate the actions choose an input $g'$ and move to $(g', t+1)$; at an AND gate the single
action moves to each input with probability $1/2$; an input gate moves to $(g, t+1)$ with reward $0$, except that a
true input in state $(g, H-1)$ pays reward $1$; states $(g, H)$ are absorbing with reward $0$. All rewards are collected at step $H - 1$, so the optimal value of
$(g_0, 0)$ is $p$ for the finite-horizon problem and $\gamma^{H-1}p$ for the discounted one, where $p$ is the largest
probability of ending at a true input. By induction on depth, every true gate has $p = 1$ and every false gate has $p < 1$, since an
AND gate averages its two inputs and an OR gate takes their maximum. The threshold
is $1$, respectively $\gamma^{H-1}$, and the construction is computable in logarithmic space.

## Expansion

This node states a precise result.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Proof prerequisite: Finite-horizon backward induction.
- Statement prerequisite: logspace many-one reductions and P-completeness.
- Proof prerequisite: polynomial-time solvability of linear programs with rational data.

## Proof depends on

- [The Circuit Value Problem is P-complete](../../../TheoryOfComputation/completeness-other-classes/circuit-value-problem/cvp-p-complete.md)

## Sources

- M. L. Littman, T. L. Dean and L. P. Kaelbling, *On the complexity of solving Markov decision problems*, UAI 1995, Section 3, reporting that Papadimitriou and Tsitsiklis showed the problem P-complete. <https://arxiv.org/pdf/1302.4971>
- C. H. Papadimitriou and J. N. Tsitsiklis, *The complexity of Markov decision processes*, Mathematics of Operations Research 12(3) (1987) 441–450, to whom Littman, Dean and Kaelbling attribute P-completeness under the expected-cost-to-target, discounted and average-cost criteria; the original paper is cited through that report. The reduction above is a self-contained argument.
