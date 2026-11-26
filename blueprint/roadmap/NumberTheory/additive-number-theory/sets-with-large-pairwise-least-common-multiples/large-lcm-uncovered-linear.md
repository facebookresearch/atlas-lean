# Erdős Problem 542, second question, corrected to integers divisible by no element

The statement that there are $c > 0$ and $n_0$ such that for every $n \ge n_0$ and every set $A \subseteq \{1, \dots, n\}$ with $1 \notin A$ and $\operatorname{lcm}(a, b) > n$ for all distinct $a, b \in A$, at least $cn$ integers $m \in \{1, \dots, n\}$ are divisible by no element of $A$.

Problem 542 as printed asks for $\gg n$ integers $m \le n$ that divide no element of $A$. That reading is trivially false: for $A$ the integers in $(n/2, n]$ every $m \le n$ has a multiple in $A$, and already for $n = 6$ and $A = \{4, 5, 6\}$ no $m$ qualifies, whereas $1, 2, 3$ are divisible by no element of $A$. The statement here is the corrected reading, counting the $m$ divisible by no element of $A$, which is the reading the refutation settles and the one formal-conjectures uses. The hypothesis $1 \notin A$ is needed, as $A = \{1\}$ leaves no such $m$.

This page records the statement as a proposition. Its refutation: [Sets with large pairwise least common multiples can leave few integers undivided](large-lcm-uncovered-linear-refuted.md).

## Sources

- T. F. Bloom, Erdős Problems, Problem #542, https://www.erdosproblems.com/542.
- Google DeepMind, formal-conjectures, ErdosProblems/542.lean, https://github.com/google-deepmind/formal-conjectures.
