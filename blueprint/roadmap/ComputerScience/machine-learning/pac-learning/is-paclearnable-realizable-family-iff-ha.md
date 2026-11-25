# The fundamental theorem of PAC learning

On a countable instance space $X$ whose singletons are measurable, a class $H$ of functions
$X \to \{0, 1\}$ is PAC learnable over its realizable distributions if and only if it has finite VC
dimension. Here PAC learnability over the realizable distributions means that for all accuracy and
confidence parameters $\varepsilon, \delta \in (0, 1)$ there are a sample size $m$ and a
deterministic learner that, for every joint distribution $D$ on $X \times \{0, 1\}$ under which
some $h \in H$ has error $0$, outputs from $m$ i.i.d. examples of $D$ a hypothesis of error at most
$\varepsilon$ with probability at least $1 - \delta$; finite VC dimension means that the finite
sets shattered by $H$ have bounded size.

The textbook theorem is stated for an arbitrary domain and leaves measurability implicit; on a
countable domain with measurable singletons every set of instances and of samples is measurable,
so the statement is a faithful special case. Asking for one sample size per accuracy and
confidence is equivalent for learnability to the textbook's "every
$m \ge m_H(\varepsilon, \delta)$". The proof of "only if" is the No-Free-Lunch argument (for every
learner and sample size, a distribution on twice as many shattered points defeats it); the proof
of "if" goes through uniform convergence, using the Sauer-Shelah lemma to bound the growth
function by a polynomial. For finite families of finite sets, the Sauer-Shelah-Pajor bound (a
family has at most as many members as the family of sets it shatters, which has at most
$\sum_{k \le d} \binom{n}{k}$ members) covers the combinatorics.

## Background

- [Every nonempty finite class is PAC learnable](occam-bound-for-consistent-learners/is-paclearnable-of-finite.md):
  the finite-class case of learnability, proved by the union bound without the VC dimension.

## Sources

- A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, *Learnability and the Vapnik-Chervonenkis dimension*, Journal of the ACM 36 (1989), 929-965.
- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press (2014), Theorem 6.7 (equivalence of items 4 and 6) and its proof in Section 6.5.
