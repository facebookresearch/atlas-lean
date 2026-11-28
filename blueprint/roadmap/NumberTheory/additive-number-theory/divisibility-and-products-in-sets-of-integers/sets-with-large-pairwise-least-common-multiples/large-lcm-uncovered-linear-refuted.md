# Sets with large pairwise least common multiples can leave few integers undivided

It is not the case that there are $c > 0$ and $n_0$ such that for every $n \ge n_0$ and every set $A \subseteq \{1, \dots, n\}$ with $1 \notin A$ and $\operatorname{lcm}(a, b) > n$ for all distinct $a, b \in A$, at least $cn$ integers $m \in \{1, \dots, n\}$ are divisible by no element of $A$.

This refutes the corrected reading of the second question of Problem 542, which counts the integers divisible by no element of $A$; as printed, the question asks for integers dividing no element of $A$, which is trivially false (for $A$ the integers in $(n/2, n]$ no $m \le n$ qualifies).

This refutes [Erdős Problem 542, second question, corrected to integers divisible by no element](large-lcm-uncovered-linear.md), the statement recorded as a proposition; the refutation is due to Schinzel and Szekeres (1959), cited under Sources.

## Sources

- T. F. Bloom, Erdős Problems, Problem #542, https://www.erdosproblems.com/542.
- A. Schinzel and G. Szekeres, Sur un problème de M. Paul Erdős, Acta Sci. Math. (Szeged) (1959), 221–229.
- Google DeepMind, formal-conjectures, ErdosProblems/542.lean, https://github.com/google-deepmind/formal-conjectures.
