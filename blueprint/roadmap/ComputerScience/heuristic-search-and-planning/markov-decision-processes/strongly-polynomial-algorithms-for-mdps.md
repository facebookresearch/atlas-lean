# Strongly polynomial algorithms for Markov decision processes

A finite discounted Markov decision process with $N \ge 1$ states, nonempty action sets, $M$ total state-action pairs, rational transition probabilities and rewards, and a rational discount factor $0 \le \gamma<1$ can be solved by linear programming in a number of arithmetic operations polynomial in $N$, $M$ and the bit size $B$ of the input. An
algorithm is *strongly polynomial* if the number of arithmetic operations is bounded by a polynomial in $N$ and
$M$ alone, with intermediate rational encodings of bit length polynomial in the input bit length.

**Question posed by the cited sources.** Is there a strongly polynomial algorithm for finite discounted Markov decision processes in
which the discount factor is part of the input (and, similarly, for average-reward processes)?

**Status (as of the sources below).** For every fixed discount factor, policy iteration is strongly polynomial
(Ye; Hansen, Miltersen and Zwick). A strongly polynomial algorithm for linear programming would yield one for
Markov decision processes; the converse is open. The general question for Markov decision processes is
distinct from strongly polynomial linear programming.

## Expansion

A good expansion separates:

1. Finite rationally encoded discounted and average-reward models, including the admissible policies, reward
    criterion, input bit length, and whether the discount factor is fixed or is part of the input. Keep
    any unichain hypothesis on a cited average-reward result explicit.
2. Optimality equations, policy iteration, and the linear-programming and occupancy-measure formulations,
    with the fixed-discount iteration bounds recorded as results with their discount-factor dependence.
3. The arithmetic-operation model used to ask the strongly polynomial question, with rational bit-size
    requirements stated explicitly, and the reduction from strongly polynomial linear programming to the
    corresponding Markov decision problem.
4. The unrestricted question as a research node, not as an established theorem. Resolving the discounted
    question does not by itself resolve a differently specified average-reward variant or the converse
    reduction to linear programming.

This page records the questions and results in the cited sources, not a certification of their present status.

## Sources

- M. L. Littman, T. L. Dean and L. P. Kaelbling, *On the complexity of solving Markov decision problems*, UAI 1995; arXiv:1302.4971, §2. <https://arxiv.org/abs/1302.4971>
- J. Huang, *Recent progress on the complexity of solving Markov decision processes* (survey write-up, Cornell ORIE), §2.3.1 and §3. <https://people.orie.cornell.edu/jh2543/prelimWriteup.pdf>
