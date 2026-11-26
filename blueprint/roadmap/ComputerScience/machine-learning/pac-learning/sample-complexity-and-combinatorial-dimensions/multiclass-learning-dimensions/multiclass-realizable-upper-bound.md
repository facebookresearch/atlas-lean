# Realizable multiclass PAC learning from finite Natarajan dimension with explicit sample size

Let $X$ be countable with measurable singletons, $\beta$ a finite label set with $k$ elements, and $C$ a class of functions $X \to \beta$ that N-shatters no finite set of more than $d$ points. Then the Boolean loss class $\{(x,y) \mapsto [c(x) \ne y] : c \in C\}$ has growth function at most $\sum_{i \le d}\binom{m}{i}\binom{k}{2}^i$, and every consistent learner (in particular every empirical risk minimizer) is an $(\varepsilon, \delta)$-PAC learner over the distributions realizable by $C$ from

$$
m \ge \frac{8}{\varepsilon}\Big(d \ln\frac{48}{\varepsilon} + 2d \ln k + \ln\frac{4}{\delta}\Big)
$$

examples, for $\varepsilon, \delta \in (0,1)$. So the realizable sample complexity is $O((d \ln(k/\varepsilon) + \ln(1/\delta))/\varepsilon)$.

## Proof sketch

The misclassification pattern of a hypothesis on labelled points is determined by its labeling of the domain points, so Natarajan's lemma bounds the growth function of the loss class. The sample size equals the binary epsilon-net sample size at confidence $\delta/k^{2d}$, and the binary argument applies verbatim to the loss class.

## Depends on

- [Multiclass fundamental theorem (Natarajan bounds)](../../../generalization-bounds-and-concentration/vc-and-natarajan-classes/multiclass-fundamental-theorem.md)
- [The realizable distribution family](../../occam-bound-for-consistent-learners/realizable-family.md)
- [A consistent learner for a finite class](../../occam-bound-for-consistent-learners/consistent-learner.md)
- [Natarajan's lemma](natarajans-lemma.md)

## Proof depends on

- [Natarajan's lemma](natarajans-lemma.md)
- [The epsilon-net theorem](../vc-sample-complexity-and-epsilon-nets/epsilon-net-theorem.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, "Understanding Machine Learning: From Theory to Algorithms", Cambridge University Press, 2014.
- B. K. Natarajan, "On Learning Sets and Functions", Machine Learning, 1989.
