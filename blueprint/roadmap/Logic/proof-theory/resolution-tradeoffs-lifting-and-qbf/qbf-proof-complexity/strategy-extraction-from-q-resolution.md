# Strategy extraction from Q-resolution refutations

From any Q-resolution or QU-resolution refutation of a false QBF one can efficiently extract a winning strategy for the universal player in which each universal variable is computed by a decision list of size polynomial in the refutation.

A **decision list** $D = (t_1, c_1), \dots, (t_n, c_n)$ is a finite sequence of pairs of a term $t_i$ and a constant $c_i \in \{0,1\}$, the last term being empty (true); under an assignment $\mu$ it evaluates to $c_i$ for the least $i$ with $\mu \models t_i$. A strategy for a universal variable $u$ is a function of the variables of smaller index; following Goultiaeva et al., it may also read the outputs of the strategy functions of universal variables of smaller index.

**Theorem.** Given a Q-resolution or QU-resolution refutation $\pi$ of a QBF $\phi$, there is a winning strategy for the universal player for $\phi$ such that each of its strategy functions for the universal variables is computable by a decision list of size polynomial in $|\pi|$; it can be constructed in time polynomial in $|\pi|$.

## Expansion

The extraction is due to Balabanov, Jiang and Widl, who represent the strategies in a form that is semantically equivalent to decision lists; the strategy for a universal variable is read off the universal reduction steps of the refutation. What the lower bound technique needs is the computational weakness of the extracted strategies: a polynomial-size decision list computes an $\mathrm{AC}^0$ function, namely $f_D = \bigvee_{i : c_i = 1} (t_i \land \bigwedge_{l < i} \neg t_l)$, a depth-two combination of terms. Hence Q-resolution and QU-resolution have strategy extraction in $\mathrm{AC}^0$.

## Depends on

- [Q-resolution and its long-distance and universal variants](q-resolution-calculi.md)

## Proof depends on

None.

## Sources

- O. Beyersdorff, L. Chew, M. Janota, "Proof complexity of resolution-based QBF calculi", *STACS 2015*, LIPIcs 30, 76-89, doi:10.4230/LIPIcs.STACS.2015.76 (Definition 9, Theorem 10 due to Balabanov, Jiang and Widl, Lemma 13).
