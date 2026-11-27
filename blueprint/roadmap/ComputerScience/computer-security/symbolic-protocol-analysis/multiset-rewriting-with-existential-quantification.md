# Multiset rewriting with existential quantification

Fix a many-sorted first-order *signature*: sorts, function symbols with argument and result sorts (constants have no arguments) and predicate symbols with
argument sorts. *Terms* are well-sorted applications of function symbols to variables and terms, and a *fact* is a ground atomic formula $P(t_1, \dots, t_n)$.
A *state* is a finite multiset of facts. A *rule* has the form

$$F_1, \dots, F_k \longrightarrow \exists x_1 \cdots \exists x_j.\ G_1, \dots, G_n$$

for atomic formulas $F_i, G_i$, its other variables being universally quantified. If a state $S$ contains $\sigma F_1, \dots, \sigma F_k$ for a ground substitution $\sigma$, the
rule rewrites $S$ to the state obtained by removing these facts (as a multiset) and adding $\sigma' G_1, \dots, \sigma' G_n$, where $\sigma'$ extends $\sigma$ by mapping
$x_1, \dots, x_j$ to distinct new constant symbols. An *MSR theory* is a signature with a set of rules; its traces are the sequences of states each obtained from the
previous one by a rule, where the constants introduced at each step are fresh for the whole trace so far: they occur in no earlier state of the trace
and not in the rules, so a constant whose last occurrence has been consumed is never chosen again. A rule *creates*, *preserves* or *consumes* $P$ facts when some $P(\vec t)$ occurs more often in its right side than in its left, every $P(\vec t)$ occurs equally often, or some
$P(\vec t)$ occurs more often in its left side; a predicate $P$ is *persistent* in a theory if every rule containing $P$ creates or preserves $P$ facts.

## Sources

- N. Durgin, P. Lincoln, J. Mitchell and A. Scedrov, "Multiset rewriting and the complexity of bounded security protocols", *Journal of Computer Security* 12(2):247–311, 2004, copy at <http://www-cs-students.stanford.edu/~nad/papers/msr-jcs215.pdf>: Section 2.1 (signatures, terms, facts, states, rules and MSR theories), Section 2.3, p. 255 (an existential chooses a new value different from the other values used in the execution) and Section 2.5 (persistence).
