# Monotone frameworks and the work-list algorithm

Let $L$ be a partially ordered set with a least element $\bot$ in which every strictly ascending chain $a_0 \sqsubset a_1 \sqsubset a_2 \sqsubset \cdots$ is finite, for example a lattice of finite height. Let a dataflow analysis of a control-flow graph with finitely many nodes $v_1, \dots, v_n$ be given by constraint functions $f_1, \dots, f_n : L^n \to L$, one per node, such that the combined function $f(x_1, \dots, x_n) = (f_1(x_1, \dots, x_n), \dots, f_n(x_1, \dots, x_n))$ is monotone on $L^n$, ordered componentwise. The solutions of the equation system $x_i = f_i(x_1, \dots, x_n)$ for $i = 1, \dots, n$ are the fixed points of $f$.

Let $\mathrm{dep}(v_i)$ be a set of nodes containing every $v_j$ for which $f_j$ depends on $x_i$: if $v_j \notin \mathrm{dep}(v_i)$, then $f_j(x_1, \dots, x_n)$ does not change when $x_i$ is replaced by any other element of $L$. The *simple work-list algorithm* starts from $x_i = \bot$ for all $i$ with a work-list $W$ holding all nodes. While $W$ is nonempty, it removes some node $v_i$ from $W$ and computes $y = f_i(x_1, \dots, x_n)$; if $y \ne x_i$, it sets $x_i = y$ and adds every node of $\mathrm{dep}(v_i)$ to $W$.

**Theorem.** Whatever node each iteration removes, every run of the simple work-list algorithm is finite. Every run that stops, that is, that reaches a state from which no iteration is possible, ends with an empty work-list and with $(x_1, \dots, x_n)$ the least fixed point of $f$, the least solution of the equation system.

## Proof sketch

Along every run, $x \sqsubseteq f(x)$, $x$ lies below every fixed point of $f$, and every node not in $W$ satisfies its equation $x_i = f_i(x_1, \dots, x_n)$; initially $W$ holds every node, and an update of $x_i$ can break only the equations of the nodes in $\mathrm{dep}(v_i)$, which it adds to $W$. So each iteration either moves $x$ strictly up in $L^n$, which has no infinite strictly ascending chain, or leaves $x$ unchanged and shrinks $W$, and every run is finite. A state from which no iteration is possible has $W = \emptyset$, so then $x$ is a fixed point of $f$ below every other.

## Remarks

When $L$ is a complete lattice, the least fixed point is also $\bigsqcup_{i \ge 0} f^i(\bot)$, reached after finitely many applications of $f$ to $\bot$, since [Kleene iteration reaches the least fixed point under the ascending chain condition](../../../Order/fixed-points-domain-theory/lfp-eq-i-sup-iterate-of-well-founded-gt.md); computing this chain is the naive fixed-point algorithm. The running time of the work-list algorithm is the subject of [its own page](running-time-of-the-simple-work-list-algorithm.md).

## Comparison with the source

Møller and Schwartzbach state the result for a complete lattice of finite height. The proof uses neither joins nor a bound on the length of chains, only a least element and the absence of infinite strictly ascending chains.

They describe $\mathrm{dep}(v)$ as the set of other nodes whose constraint functions read the variable of $v$. A node whose own constraint function reads its own variable has to belong to its own dependency set: with one node, $L = \{0 \sqsubset 1 \sqsubset 2\}$, $f_1(0) = 1$, $f_1(1) = f_1(2) = 2$ and $\mathrm{dep}(v_1) = \emptyset$, the algorithm stops after one iteration with $x_1 = 1$, while the least solution is $x_1 = 2$.

## Sources

- A. Møller and M. I. Schwartzbach, *Static Program Analysis*, lecture notes, Aarhus University, version of October 15, 2026, <https://cs.au.dk/~amoeller/spa/>, Section 4.4 (equation systems and their least solutions, pp. 46–48) and Section 5.3 (the simple work-list algorithm and its termination and correctness, pp. 60–61)
