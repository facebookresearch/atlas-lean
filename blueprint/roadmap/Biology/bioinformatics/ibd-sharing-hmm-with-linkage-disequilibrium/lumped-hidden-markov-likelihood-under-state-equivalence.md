# Lumped hidden Markov likelihood under state equivalence

**Hidden Markov model.** Let hidden states $S_1, \dots, S_L$ take values in a finite set $\mathcal{S}$
and observations $X_1, \dots, X_L$ be conditionally independent given the states, with emission
probabilities $P(x_i \mid s_i)$, transition probabilities $P(s_i \mid s_{i-1})$ and initial law
$P(s_1)$. The likelihood

$$P(x_1, \dots, x_L) = \sum_{s_1, \dots, s_L} P(s_1) P(x_1 \mid s_1) \prod_{i=2}^{L} P(s_i \mid s_{i-1})
 P(x_i \mid s_i)$$

is computed by the forward recursion in $O(L |\mathcal{S}|^2)$ time.

**State equivalence.** Let $\mathcal{S}$ be partitioned into equivalence classes $[s]$ such that

- **Condition I:** $P(x_i \mid s) = P(x_i \mid s')$ for all $s, s'$ in the same class and every $x_i$;
- **Condition II:** the transition probability into a class,
  $P([s] \mid s') = \sum_{u \in [s]} P(u \mid s')$, takes the same value for all $s'$ in a given class.

Define $P(x_i \mid [s]) = P(x_i \mid s)$, $P([s] \mid [s']) = P([s] \mid s')$ and
$P([s]) = \sum_{u \in [s]} P(u)$.

**Proposition.** Under Conditions I and II,

$$P(x_1, \dots, x_L) = \sum_{[s_1], \dots, [s_L]} P([s_1]) P(x_1 \mid [s_1]) \prod_{i=2}^{L}
 P([s_i] \mid [s_{i-1}])\, P(x_i \mid [s_i]),$$

so the forward algorithm runs on the classes, in time quadratic in the number of classes rather
than in $|\mathcal{S}|$.

## Depends on

- [Likelihood of the observations](../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood.md)
- [The forward algorithm computes the likelihood](../../../ComputerScience/machine-learning/probabilistic-graphical-models/hidden-markov-models/likelihood-eq-sum-forward.md)
- [Strong lumpability onto the image of a finite Markov chain](../../../Probability/markov-chains/finite-markov-chains/strong-lumpability-of-finite-markov-chains.md)

## Expansion

Condition II is ordinary (strong) lumpability of the hidden chain: the class process
$[S_1], [S_2], \dots$ is itself a Markov chain with transitions $P([s] \mid [s'])$. Condition I says
the observations depend on the hidden state only through its class. Together they make the joint
law of (class sequence, observations) a hidden Markov model in its own right, and summing over the
states inside each class in the forward recursion yields exactly the lumped recursion. In pedigree
linkage and identity-by-descent analysis, the hidden state is an inheritance vector whose size grows
exponentially with the number of meioses; choosing classes that respect both conditions is what
turns exponential state spaces into polynomial ones while leaving the likelihood unchanged.

## Sources

- S. Bercovici, C. Meek, Y. Wexler, D. Geiger, "Estimating genome-wide IBD sharing from SNP data via
  an efficient hidden Markov model of LD with application to gene mapping", Bioinformatics 26 (2010)
  i175-i182, Section 2, Eqs. (1)-(3) and Conditions I-II, <https://doi.org/10.1093/bioinformatics/btq204>
  (PMC2881389).
